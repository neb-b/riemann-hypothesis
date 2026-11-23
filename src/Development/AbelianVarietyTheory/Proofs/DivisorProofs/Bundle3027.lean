module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTwistOfLowers
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTranslateLiesOverProductTorsionFra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalRingLinearHomSchemeLowerObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem exists_baseSch : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b) (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)), b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧ IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧ ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b → ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂)) (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧ (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f)) (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧ (letI := ((residue W).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) :=
  BaseSch.exists_baseSch_of_homScheme GlobalTheory.UCanonHom.homScheme_low

end GlobalTheory.UCanon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyOpenThetaRingRegular
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_opens_R_le_O : ∀ X₁ : GlobalTheory.GSep.GSet, ∃ U : X₁.M.Z.Opens, (U : Set X₁.M.Z).Nonempty ∧
    ∀ z ∈ U, X₁.S.R ≤ X₁.M.O z := by
  intro X₁
  obtain ⟨s, hs⟩ := X₁.S.fg
  refine ⟨⟨⋂ x ∈ s, {z | x ∈ X₁.M.O z}, isOpen_biInter_finset fun x _ => X₁.M.isOpen_setOf_mem_O x⟩,
    ⟨genericPoint X₁.M.Z, ?_⟩, ?_⟩
  · show genericPoint X₁.M.Z ∈ ⋂ x ∈ s, {z | x ∈ X₁.M.O z}
    refine Set.mem_iInter₂.2 fun x _ => ?_
    show x ∈ X₁.M.O (genericPoint X₁.M.Z)
    rw [RatModel.O_genericPoint]
    exact Algebra.mem_top
  · intro z hz
    have hz' : z ∈ ⋂ x ∈ s, {z | x ∈ X₁.M.O z} := hz
    rw [← hs]
    exact Algebra.adjoin_le fun x hx => Set.mem_iInter₂.1 hz' x hx

end GlobalTheory.GSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjectMapsOfDualNumberIdentifications
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.EpsObj

theorem act_comm_eps : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → ∀ (u : G' ⟶ G') [IsMonHom u] (v : G ⟶ G) [IsMonHom v], u.left ≫ φ₁ = φ₁ ≫ v.left → u.left ≫ φ₂ = φ₂ ≫ v.left := _root_.GlobalTheory.EpsRigid.comm_of_comm

theorem sec_eps : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₁ g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₁ = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₂ → ∀ (n : ℕ), (n : k) ≠ 0 → ∀ (σ : 𝟙_ (Over S) ⟶ G), σ ^ n = 1 → ∀ (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ G'), x ^ n = 1 → x.left ≫ φ₁ = g₁ ≫ σ.left → x.left ≫ φ₂ = g₂ ≫ σ.left := _root_.GlobalTheory.UCanon.torsion_sec_over_second

theorem spMap_comp_eps {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eta_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) (n : ℕ) :
    p.eta a ^ n = p.eta (n • a) := by
  induction n with
  | zero =>
    have h := p.eta_add 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | succ n ih => rw [pow_succ, ih, succ_nsmul, p.eta_add]

theorem etaA_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) (n : ℕ) :
    p.etaA a ^ n = p.etaA (n • a) := by
  induction n with
  | zero =>
    have h := p.etaA_add 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | succ n ih => rw [pow_succ, ih, succ_nsmul, p.etaA_add]

theorem eta_pow_M {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) :
    p.eta a ^ l.M = 1 := by
  rw [eta_pow]
  apply p.eta_ker
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at this
    first | exact Ideal.mul_le_left this | exact Ideal.mul_le_right this
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hM Submodule.mem_top

theorem etaA_pow_A {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) :
    p.etaA a ^ l.A = 1 := by
  rw [etaA_pow]
  exact p.etaA_ker a

theorem exists_objMaps : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (W : Type) [CommRing W] (b : c.F →+* W) (o : LowObj D' c b) (k : Type) [Field k] (f : W →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ o.t.G.left), IsGrpPullback B' o.t.G (spMap f) π₁ → IsGrpPullback B' o.t.G (spMap (GlobalTheory.RigChart.constHom f)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → LBIso (o.t.PP.L.pull π₁) (o.t.PP.L.pull π₂) → ∃ (o' : LowObj D' c (f.comp b)) (m₁ : ObjMap o' o (spMap f)) (m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f))) (io : o'.t.G.left ≅ B'.left), io.hom ≫ B'.hom = o'.t.G.hom ∧ m₁.toSABMap.φ = io.hom ≫ π₁ ∧ m₂.toSABMap.φ = io.hom ≫ π₂ := by
  intro E _ _ _ H D' l c W _ b o k _ f B' _ π₁ π₂ h₁ h₂ h0 hL
  have hlow : lowMap c (f.comp b) = spMap f ≫ lowMap c b := by
    unfold lowMap
    rw [RingHom.comp_assoc, spMap_comp_eps]
  obtain ⟨o', ⟨m₀⟩⟩ : ∃ o' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (lowMap c (f.comp b)),
      Nonempty (ObjMap o' o (spMap f)) := by
    rw [hlow]
    exact GlobalTheory.LevelGroup.pull_univ o (spMap f)
  let io : o'.t.G.left ≅ B'.left := IsPullback.isoIsPullback _ _ m₀.cart.1 h₁.1
  have io₁ : io.hom ≫ π₁ = m₀.toSABMap.φ := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have io₂ : io.hom ≫ B'.hom = o'.t.G.hom := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hio : IsGrpPullback o'.t.G B' (𝟙 _) io.hom :=
    IsGrpPullback.cancel h₁ (by rw [Category.id_comp, io₁]; exact m₀.cart) (by rw [io₂, Category.comp_id])
  have hψc : IsGrpPullback o'.t.G o.t.G (spMap (GlobalTheory.RigChart.constHom f)) (io.hom ≫ π₂) := by
    have := hio.comp h₂
    rwa [Category.id_comp] at this
  have h0' : ∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k),
      x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
        x ≫ m₀.toSABMap.φ = x ≫ io.hom ≫ π₂ := by
    intro Z x y hx
    rw [← io₁, ← Category.assoc, ← Category.assoc]
    exact h0 Z (x ≫ io.hom) y (by rw [Category.assoc, io₂, hx])
  have hA' : IsAbelianScheme o'.t.G :=
    ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  have hact : ∀ a, (o'.t.act.act a).left ≫ io.hom ≫ π₂ = (io.hom ≫ π₂) ≫ (o.t.act.act a).left := fun a => by
    haveI := o'.t.act.hom a
    haveI := o.t.act.hom a
    exact act_comm_eps k o'.t.G hA' o.t.G _ _ _ hψc h0' (o'.t.act.act a) (o.t.act.act a) (m₀.act a)
  have hLB : LBIso o'.t.PP.L (o.t.PP.L.pull (io.hom ≫ π₂)) := by
    obtain ⟨w, hw, -⟩ := m₀.lin
    have e₁ : LBIso o'.t.PP.L (o.t.PP.L.pull (io.hom ≫ π₁)) := by
      rw [io₁]
      exact ⟨w, hw⟩
    have e₂ : LBIso (o.t.PP.L.pull (io.hom ≫ π₁)) (o.t.PP.L.pull (io.hom ≫ π₂)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp io.hom rfl rfl hL
    exact LBIso.trans o'.t.PP.isLB (pull_isLB o.t.PP.isLB _) (pull_isLB o.t.PP.isLB _) e₁ e₂
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper o'.t o.t (spMap (GlobalTheory.RigChart.constHom f)) (io.hom ≫ π₂) o.proper hψc hact hLB
  have hg : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap f =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (GlobalTheory.RigChart.constHom f) := by
    rw [← spMap_comp_eps, ← spMap_comp_eps]
    congr 1
  have hunit : ∀ n : ℕ, 0 < n → (n : k) ≠ 0 := by
    intro n hn
    have := ((baseKA (LowDat.lowLevel l)).unit n hn).map
      (((TrivSqZeroExt.fstHom k k k).toRingHom.comp (f.comp b)).comp
        (IntermediateField.inclusion (LowDat.ka_le l c)).toRingHom)
    rw [map_natCast] at this
    exact this.ne_zero
  have hsec : ∀ (σ : 𝟙_ (Over (Sp W)) ⟶ o.t.G) (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G) (n : ℕ), 0 < n →
      σ ^ n = 1 → x ^ n = 1 → x.left ≫ m₀.toSABMap.φ = spMap f ≫ σ.left →
        x.left ≫ io.hom ≫ π₂ = spMap (GlobalTheory.RigChart.constHom f) ≫ σ.left :=
    fun σ x n hn hσ hx hx₁ => sec_eps k o'.t.G hA' o.t.G _ _ _ _ hψc h0' hg n (hunit n hn) σ hσ x hx hx₁
  have hMpos : 0 < (LowDat.lowLevel l).M := by have := (LowDat.lowLevel l).three_le; omega
  let m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f)) :=
    { toSABMap := m
      eta := fun a => by
        show (o'.eta a).left ≫ m.φ = _
        rw [hm]
        exact hsec _ _ _ hMpos (eta_pow_M o a) (eta_pow_M o' a) (m₀.eta a)
      etaA := fun a => by
        show (o'.etaA a).left ≫ m.φ = _
        rw [hm]
        exact hsec _ _ _ (LowDat.lowLevel l).A_pos (etaA_pow_A o a) (etaA_pow_A o' a) (m₀.etaA a) }
  exact ⟨o', m₀, m₂, io, io₂, io₁.symm, hm⟩

end GlobalTheory.UCanon.EpsObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionMember
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_points_frames_theta : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1) (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧ (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧ (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ ρ.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  have hj : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have gp := 𝔪.cart
  have hsq : ∀ a, (spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ≫ X₁.ρ.P.A.hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    intro a
    rw [Category.assoc, Over.w (X₁.ρ.pt a), hj]
    simp
  let x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) := fun a =>
    Over.homMk (gp.1.lift _ _ (hsq a)) (gp.1.lift_snd _ _ _)
  have hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left := fun a => gp.1.lift_fst _ _ _
  obtain ⟨rig, fr, hrig, -, hfr⟩ := GlobalTheory.exists_frames_move_through (T := baseOver (Sp X₁.S.R))
    (T' := TFK (R := V) (FractionRing V)) (h := spMap 𝔪.yK) gp 𝔪.wl_gen X₁.ρ.rig_gen hx X₁.ρ.fr_tors
  have hτ : (spMap 𝔪.yK : (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left) ≫
      (baseOver (Sp X₁.S.R)).hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    rw [hj]; simp
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB (a := 1) X₁.ρ.th₁
  refine ⟨x, fr, th, rig, hx, fun a => ⟨(hfr a).1.2.1, fun z J J' hJ hJ' => ?_⟩, fun a => ?_, hrig, fun a => (hfr a).1⟩
  · have e := (hfr a).2 _ (𝟙 _) z J J' hJ hJ'
    rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at e
    exact e.symm
  · have hv := GlobalTheory.ThetaPtMove.isValueAt_move (T := TFK (R := V) (FractionRing V))
      (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) X₁.ρ.P.isLB 𝔪.A.isLB (a := 1)
      (x := x a) (x₀ := X₁.ρ.pt a) (hx a).symm (ρ₀ := X₁.ρ.fr a) (ρ := fr a) (hfr a).2 (s₀ := X₁.ρ.th₁) (s := th) hth
      (X₁.ρ.th_val a)
    intro z J hJ
    have e := GlobalTheory.FrameMove.sval_valueAt hv (𝟙 _) hJ
    rw [Category.id_comp] at e
    refine e.trans ?_
    rw [GlobalTheory.FrameMove.val_powFrame, Nat.cast_one, zpow_one]
    congr 1
    exact (gs_pull (𝟙 _) (spMap 𝔪.yK) z ⊤ trivial _).trans
      ((congrArg (fun q => gs q z ⊤ _) (Category.id_comp _)).trans (GlobalTheory.FrameMove.gs_spMap 𝔪.yK z _))

end GlobalTheory.GSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigTorsFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep.TwistTranslate
open GlobalTheory.UT.CoefBasic GlobalTheory.AdicSum GlobalTheory.Poinc.Tors.AnyField GlobalTheory.Poinc.Tors.ValPair GlobalTheory.Poinc.Tors.Translate

variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

theorem x_add (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A))
    (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) (a τ : X₁.S.Gam)
    (xτ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (hτ : xτ.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) :
    x (a + τ) = x a * xτ := by
  let U : Over.mk ((TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk (spMap 𝔪.yK) (by
      show spMap 𝔪.yK ≫ 𝟙 _ = _
      rw [Category.comp_id]
      change _ = Spec.map (𝟙 _) ≫ _
      rw [Spec.map_id, Category.id_comp])
  have key := 𝔪.cart.2 (TFK (R := V) (FractionRing V)) (x a) xτ (U ≫ X₁.ρ.pt a) (U ≫ X₁.ρ.pt τ)
    (hx a).symm hτ.symm
  rw [← MonObj.comp_mul, ← X₁.ρ.pt_add] at key
  apply Over.OverMorphism.ext
  refine 𝔪.cart.1.hom_ext ?_ ?_
  · rw [hx (a + τ), ← key]; rfl
  · rw [Over.w, Over.w]

theorem eq_yK_zeta_pow (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (u : FractionRing V)
    (hu : u ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1) : ∃ e : ℕ, u = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) := IsFractionRing.charZero V
  set k := (X₁.S.r * X₁.S.N) ^ 2 with hk
  have hkpos : 0 < k := by
    have h1 := X₁.S.r_pos; have h2 := X₁.S.N_ge
    positivity
  have hinj : Function.Injective (algebraMap X₁.o₁ X₁.S.R) := by
    intro a b hab
    apply X₁.ar.inj
    have := congrArg (fun x : X₁.S.R => (x : X₁.Ω₁)) hab
    simpa using this
  have hR : IsPrimitiveRoot (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) k := X₁.S.prim.map_of_injective hinj
  have hroot : (Polynomial.cyclotomic k (FractionRing V)).IsRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) := by
    have h := (hR.isRoot_cyclotomic hkpos).map (f := 𝔪.yK)
    rwa [Polynomial.map_cyclotomic] at h
  haveI : NeZero (k : FractionRing V) := ⟨by exact_mod_cast hkpos.ne'⟩
  have hK : IsPrimitiveRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) k :=
    (Polynomial.isRoot_cyclotomic_iff).1 hroot
  obtain ⟨e, -, he⟩ := hK.eq_pow_of_pow_eq_one hu
  exact ⟨e, by rw [map_pow, map_pow, he]⟩

theorem exists_rig_torsFrame (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ)
    (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a))
    (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left)
    (hfr : ∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) :
    ∃ ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A)), ρA.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  have gp := 𝔪.cart
  have hw := 𝔪.wl_gen
  obtain ⟨rig', hrig', Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) hw X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm gp) X₁.ρ.rig X₁.ρ.rig_gen
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over _)).left) (z : Z) J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      GlobalTheory.FrameMove.rval X₁.ρ.rig (r ≫ spMap 𝔪.yK) z J =
        GlobalTheory.ConstFam.wVal 𝔪.wl z J J' (r ≫ eSec 𝔪.A.A) * GlobalTheory.FrameMove.rval rig' r z J' :=
    fun Z r z J J' hJ hJ' =>
      (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  refine ⟨rig', hrig', fun a => ?_⟩
  exact GlobalTheory.FrameMove.isTorsFrame_move gp hw hr (hx a) (X₁.ρ.fr_tors a) (hfr a).1
    (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)

theorem over_translate (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (w₀ : W0 𝔪.U.toUnifPre) (hw₀ : w₀.IsGen)
    (ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρA.IsGen) (x₁ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)
    (e₁ : FrAt x₁) (he₁ : IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) x₁ e₁)
    (g₁ : GtPtF 𝔪.D.toPre (FractionRing V)) (w₁ : Frm 𝔪.D.toPre (FractionRing V) 1 g₁.b)
    (hg₁ : ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₁ o ∧ o.IsZero) (hw₁ : w₁.IsGen) (H₁ : 𝔪.Over' w₀ g₁ w₁ x₁ e₁)
    (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) (hχ : χ ^ (X₁.S.r * X₁.S.N) = 1)
    (g₀ : GtPtF 𝔪.D.toPre (FractionRing V)) (ht : IsTor χ g₀)
    (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)
    (_ : p.y = 0) (hp : p.g = g₀) (hx : QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x)
    (g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (hadd : g₁.IsAdd g₀ g₂) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b)
    (hww : ∀ z J, Good 𝔪.D.toPre.P.L z J → val w₂ (𝟙 _) z J = val w₁ (𝟙 _) z J)
    (x₂ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (hx₂ : x₂ = x₁ * x) :
    ∃ e₂ : FrAt x₂, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) x₂ e₂ ∧ 𝔪.Over' w₀ g₂ w₂ x₂ e₂ := by
  obtain ⟨o, ho, _⟩ := hg₁
  subst hp
  have hB : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  haveI := 𝔪.cn.2.2.2
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (lt_of_lt_of_le two_pos X₁.S.N_ge)
  obtain ⟨w, hw, vw⟩ := exists_gen 𝔪.D.toPre.P.isLB (φ' := DegPre.lineφ 𝔪.D.toPre _ g₂.b) (ε' := DegPre.lineε 1)
    (fun U _ h => by rw [(ThetaAverage.val_translate ht hadd).1]) w₁ hw₁
  have vw' := fun z J hJ => vw _ (𝟙 _) z J hJ
  obtain ⟨e₂, he₂, H₂⟩ := exists_liesOver hB 𝔪.semi 𝔪.U hw₀ hn hw₁ he₁.2.1 H₁ hχ p ht hx hadd hw vw' hx₂
  refine ⟨e₂, isTorsFrame_of_liesOver hB 𝔪.semi 𝔪.U hw₀ hρ hn ho hw₁ he₁ H₁ hχ ht hadd hw vw' ?_ he₂ H₂,
    fun k hk wk e => H₂ k hk wk fun z J hJ => by rw [e z J hJ, hww z J hJ, vw' z J hJ]⟩
  rw [hx₂, mul_pow, he₁.1, (hx w₀ hw₀).1, _root_.mul_one]


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem twistSum_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → ∃ e : ℕ, SumF (maximalIdeal V) (FractionRing V) (fun mu : X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀ C lab _ T hT c τ _ χ hχ hyp
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hTc⟩ := hT
  obtain ⟨ρA, hρA, htors⟩ := exists_rig_torsFrame 𝔪 x fr hx hfr
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' c) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w'', hw''g, hw''v⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w''.IsGen ∧ ∀ z J, val w'' (𝟙 _) z J = val (w c) (𝟙 _) z J := by
    revert hb
    generalize (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w c, (hc c).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := over_translate 𝔪 w₀ hw₀ ρA hρA (x (lab c)) (fr (lab c)) (htors _)
    (g' c) (w c) (hc c).1 (hc c).2.1 (hc c).2.2 χ hχ _ hg₀ p xτ hpy hpg hq _ hadd w'' (fun z J _ => hw''v z J)
    (x (lab c + τ)) (x_add 𝔪 x hx (lab c) τ xτ hxτ)
  obtain ⟨u, hu, hval⟩ := GlobalTheory.Poinc.TorsRatio.valAt_torsFrame_ratio V 𝔪.A ρA hρA _
    (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) _ _ _
    (htors (lab c + τ)) he₂ th _ (hth (lab c + τ))
  have hsum := hov 1 le_rfl w'' (fun z J _ => (pow_one _).symm) hw''g th s _ hs hval
  obtain ⟨e, he⟩ := eq_yK_zeta_pow 𝔪 u hu
  refine ⟨e, ?_⟩
  rw [← he]
  have hco : ∀ χ', coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w'' χ' =
      ((χ (Multiplicative.ofAdd χ') : (FractionRing V)ˣ) : FractionRing V) * coef s (g' c) (w c) χ' := fun χ' => by
    rw [GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd (hc c).2.1 (c := 1) (fun z J _ => by rw [hw''v, map_one, _root_.one_mul]) s χ',
      _root_.one_mul]
  have hA := admissibleBase_of_completeNormalLocalCharZero 𝔪.cn
  have key := ((GlobalTheory.AdicSum.sumF_calculus V _ hA (FractionRing V) _
    (coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w'') 0 _ 0).2.2 X 𝔪.e₈
    𝔪.e₈.injective (fun j hj => absurd ⟨𝔪.e₈.symm j, 𝔪.e₈.apply_symm_apply j⟩ hj)).2 hsum
  convert key using 2 with mu
  simp only [Function.comp_apply, hco, hTc]

end GlobalTheory.GSep.TwistTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRouteDatumTranslationCombinationGoodPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

namespace GlobalTheory.SmallDatum

theorem exists_datum_comb_mem_So : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB ∧ ∃ z : GA D (G.V (.grid i j)) →₀ ℂ, zdeg z ≠ 0 ∧
      (z.sum fun k c => c • om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ k, 1) ΦB) ∈ Γ.M'.So Bs.ψ Bs.τ₁ := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ΦB, hD, m, f, φ, φ₀, rfl, hSB, hvac, h₀, ι, P, Λ, c, hι, hφ₀⟩ :=
    GlobalTheory.T.exists_routeDatum_finite_pureTensors_vacuum hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ν, α, hν, hact⟩ := _root_.GlobalTheory.LocWeilAct.act_omB W t i j M e Bs Γ X om om' h hTr
  exact ⟨_, hD, GlobalTheory.T.exists_goodPlace_translateCombination_latticeIndicator Bs Γ hTr.geo.hM' hTr.geo.lt om' _ ν α hν ι hι (hact ι hι) f φ φ₀ hSB hvac h₀ P Λ c hφ₀⟩

end GlobalTheory.SmallDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantNeZeroUniformisedMember
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem GMem.exists_th_ne_zero : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ b, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) :=
    (RingHom.charZero_iff (IsFractionRing.injective V (FractionRing V))).1 inferInstance
  exact GlobalTheory.ThetaGeneric.exists_th_ne_zero GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 _ _ X₁.S X₁.ρ
    (FractionRing V) 𝔪.yK

end GlobalTheory.GSep

end
end

