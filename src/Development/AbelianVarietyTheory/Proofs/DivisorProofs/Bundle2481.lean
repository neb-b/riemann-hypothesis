module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2018
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointsFirstCoordinateUnramifiedSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonempty
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.CompHS.TorFlagEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem torFlag_of_model (Y : Model Xo c (RingHom.id c.F)) (hs : SmoothOfRelativeDimension Dw.dim Y.s)
    (hb : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (LogKS.boundary Y)) (hk : LogKS.HasLogKS Y.t Y.s (LogKS.interior Y))
    (hp : PushInvertible Y.t.G Y.t.PP.L) : Nonempty (TorFlag Xo c) :=
  ⟨⟨Y, hs, hb, hk, (_root_.GlobalTheory.FlagMod.FieldFlag.nonempty_flagModel E H Dw l Xo c Y hs hp).some⟩⟩

end GlobalTheory.CompHS.TorFlagEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedUnramifiedCompleteTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnramTorsPull

theorem torsion_fixed_unramified : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → ∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hR D A G _ _ hG U W hW V _ _ _ φ hV hφ hcl n hn hnu j
  obtain ⟨hdvr, -, -⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  letI : Algebra (FractionRing R) (AlgebraicClosure (FractionRing V)) :=
    ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (IsLocalization.map (FractionRing V) φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ) :
        FractionRing R →+* FractionRing V)).toAlgebra
  have hc : ∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r)) := fun r => by
    show algebraMap (FractionRing V) _ (IsLocalization.map _ _ _ (algebraMap R _ r)) = _
    rw [IsLocalization.map_eq]
  have hk : IsUnit ((n ^ j : ℕ) : V) := by rw [Nat.cast_pow]; exact hnu.pow j
  obtain ⟨T₁, h₁, hb⟩ := _root_.GlobalTheory.DivPtsUnram.divPts_unram R D.toPre V φ hV hc (n ^ j) hk
  obtain ⟨T', h₂, hQ⟩ := _root_.GlobalTheory.UnramCharVals.qk_fixed_of_unram R hR D W hW V φ hV hφ hcl hc (n ^ j) hk T₁ h₁ hb
  have hT := h₁.trans h₂
  have hmem := hT.mem
  obtain ⟨hdvr', f, hf, hirr⟩ := hT
  refine ⟨T', hdvr', f, hf, hirr, fun σ hσ x hx => ?_⟩
  exact GlobalTheory.T.torsion_fixed_of_quotientClasses_fixed R hR D A G hG U V φ hc (n ^ j) (Nat.one_le_pow _ _ (by omega)) σ (fun v => hσ _ (hmem v)) (hQ σ hσ) x hx

end GlobalTheory.UnramTorsPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelEqWeilPairingToricTorsionPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

namespace GlobalTheory.Poinc.UTestLabel

theorem char_eq_weil_of_label : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ∃ sg : ℤˣ, ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (b : S.Gam), τ' ^ (S.r * S.N) = 1 → (∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left) → ∀ (a : S.Gam) (β : u.D.toPre.X), l.yy a = QuotientAddGroup.mk β → ((τ' (Multiplicative.ofAdd β) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * ((sg : ℤ) • eStd S.g _ b a).val))) := by
  intro o Ω _ _ _ S ρ
  refine ⟨1, ?_⟩
  intro p _ y₀ u l τ' b hτ hb a β hβ
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hk : 1 ≤ S.r * S.N :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega))
  haveI : CharZero u.V := CharZero.mk (fun m n hmn => by
    have e0 := congrArg ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))) hmn
    simpa only [map_natCast, Nat.cast_inj] using e0)
  obtain ⟨f, hf1, -, -, -, hfW⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hk
  obtain ⟨pk, x, hpkx, hxo⟩ := GlobalTheory.Poinc.exists_qkPt_of_utest o Ω S ρ p y₀ u a
  obtain ⟨q, hqy, hqt⟩ := exists_qkPt_tor u.D.tau_bimult τ' hτ
  have hqx : QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (f q) := (hf1 q (f q)).2 rfl
  have hqo := hb q (f q) hqy hqt hqx
  have hpk : x = f pk := (hf1 pk x).1 hpkx
  have W₁ := weilQkIs_tor hG q pk hqy hqt
  have W₂ := (hfW q pk (τ' (Multiplicative.ofAdd pk.y))).1 W₁
  have := ρ.P.isAb.comm
  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    have e1 : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK =
        spMap ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp u.yK) := (spMap_comp _ _).symm
    rw [e1, u.fac]
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) (by simp)
  have hh : h.left = spMap y₀ := hy
  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) :=
    S.prim.pow (pow_pos hk 2) (pow_two _)
  let c₀ : (S.R)ˣ := Units.map (algebraMap o S.R).toMonoidHom (hζ.isUnit (by omega)).unit
  have w := GlobalTheory.CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB h
    (ρ.weil b a (c₀ ^ (eStd S.g _ b a).val) (by rw [pow_mul, map_pow]; rfl))
  have W₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ ρ.P.isLB u.A.isLB u.cart u.lb
    (TFK (R := u.V) (PadicAlgCl p)) _ (f q) (f pk) (h ≫ ρ.pt b) (h ≫ ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB W₂ W₃)
    have e' := congrArg Units.val e
    simp only [MonoidHom.coe_coe, Units.coe_map, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec,
      RingHom.toMonoidHom_eq_coe] at e'
    have hq : (QuotientAddGroup.mk β : u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range) =
        QuotientAddGroup.mk pk.y := hβ.symm.trans (l.yy_eq a pk x hpkx hxo)
    obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.1 (QuotientAddGroup.eq.1 hq)
    have hpy : pk.y = β + (S.r * S.N) • m := by
      rw [nsmulAddMonoidHom_apply] at hm
      rw [hm]; abel
    have hτm : τ' (Multiplicative.ofAdd ((S.r * S.N) • m)) = 1 := by
      rw [ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    rw [hpy, ofAdd_add, map_mul, hτm, _root_.mul_one] at e'
    rw [e', Units.val_one, one_smul, ← map_pow, ← pow_mul]
  · show h.left ≫ (ρ.pt b).left = _
    rw [hh, hqo]
  · show h.left ≫ (ρ.pt a).left = _
    rw [hh, ← hxo, hpk]

end GlobalTheory.Poinc.UTestLabel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelingsEqOfThetaPointPairingsOrderN
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LabelRigid

open GlobalTheory.LevelOfPairing

section Abstract

variable {G U : Type} [Group G] [CommGroup U] {W : G → G → U → Prop} {M : ℕ}

theorem eq_of_pairing (cm : ∀ a b : G, Commute a b)
    (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hn : ∀ x : G, x ^ M = 1 → (∀ y, y ^ M = 1 → W x y 1) → x = 1) {a b : G} (ha : a ^ M = 1) (hb : b ^ M = 1)
    (h : ∀ y, y ^ M = 1 → ∃ c, W a y c ∧ W b y c) : a = b := by
  have ha' : a⁻¹ ^ M = 1 := by rw [inv_pow, ha, inv_one]
  refine inv_mul_eq_one.1 (hn _ (by rw [(cm _ _).mul_pow, ha', hb, _root_.mul_one]) fun y hy => ?_)
  obtain ⟨c, h₁, h₂⟩ := h y hy
  obtain ⟨d, hd, -⟩ := hu _ y ha' hy
  have e := hm _ _ _ _ _ hd h₁
  rw [inv_mul_cancel] at e
  exact (hu 1 y (one_pow _) hy).unique e (rel_one hu hm hy) ▸ hm _ _ _ _ _ hd h₂

theorem comb_eq (cm : ∀ a b : G, Commute a b)
    (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hn : ∀ x : G, x ^ M = 1 → (∀ y, y ^ M = 1 → W x y 1) → x = 1) {I : Type} {y₁ y₂ : I → G}
    (t₁ : ∀ p, y₁ p ^ M = 1) (t₂ : ∀ p, y₂ p ^ M = 1) (s₂ : ∀ y, y ^ M = 1 → ∃ p, y₂ p = y)
    (hw : ∀ p q c, W (y₁ p) (y₁ q) c → W (y₂ p) (y₂ q) c) {r : ℕ} (b : Fin r → I) (a : Fin r → ℕ) (p : I)
    (hp : y₁ p = (List.ofFn fun i => y₁ (b i) ^ a i).prod) : y₂ p = (List.ofFn fun i => y₂ (b i) ^ a i).prod := by
  refine eq_of_pairing cm hu hm hn (t₂ p) (prod_pow_eq_one cm _ (fun i => t₂ (b i)) a) fun y hy => ?_
  obtain ⟨q, rfl⟩ := s₂ y hy
  choose c hc using fun i => (hu _ _ (t₁ (b i)) (t₁ q)).exists
  have o₁ := rel_one hu hm (t₁ q)
  have o₂ := rel_one hu hm (t₂ q)
  refine ⟨∏ i, c i ^ a i, hw _ _ _ ?_, rel_prod hm o₂ _ _ fun i => rel_pow hm o₂ (hw _ _ _ (hc i)) _⟩
  rw [hp]
  exact rel_prod hm o₁ _ _ fun i => rel_pow hm o₁ (hc i) _

end Abstract

theorem eq_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)) {n j m : ℕ}
    (hn : n.Prime) (ho : Odd n) (hm : m = n ^ j * (n ^ 2) ^ 2) (hb : ((n ^ 2) ^ 2) ^ P.g * P.g.factorial < m)
    {I : Type} {y₁ y₂ : I → (baseOver (Sp K) ⟶ P.A)}
    (t₁ : ∀ p, y₁ p ^ (m ^ 2) = 1) (t₂ : ∀ p, y₂ p ^ (m ^ 2) = 1)
    (s₁ : ∀ y, y ^ (m ^ 2) = 1 → ∃ p, y₁ p = y) (s₂ : ∀ y, y ^ (m ^ 2) = 1 → ∃ p, y₂ p = y)
    (hw : ∀ p q c, WeilIs P.A P.L (m ^ 2 : ℕ) (y₁ p) (y₁ q) c → WeilIs P.A P.L (m ^ 2 : ℕ) (y₂ p) (y₂ q) c)
    (hfix : ∀ p, y₁ p ^ n = 1 → y₂ p = y₁ p) {v : I → Γ((baseOver (Sp K)).left, ⊤)}
    (v₁ : IsThetaPt P m y₁ v) (v₂ : IsThetaPt P m y₂ v) (p : I) : y₂ p = y₁ p := by
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have cm : ∀ a b : baseOver (Sp K) ⟶ P.A, Commute a b := fun a b => _root_.mul_comm a b
  have hm0 : m ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
  have hK : ((m ^ 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hm0
  have : NeZero (m ^ 2) := ⟨hm0⟩
  have : NeZero ((m ^ 2 : ℕ) : K) := ⟨hK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (m ^ 2)
  have hζ := hz.isUnit_unit (NeZero.ne _)
  generalize (hz.isUnit (NeZero.ne _)).unit = ζ at hζ
  obtain ⟨lev⟩ := GlobalTheory.nonempty_level_of_isAlgClosed K P (m ^ 2) ζ hK hζ
  obtain ⟨hu, hmul, -⟩ := hL.weil _ P (m ^ 2) (baseOver (Sp K))
  have hnd := hL.weilNondeg K P (m ^ 2) hK
  choose b hb' using fun i => s₁ _ (lev.torsion i)
  have eb : lev.pt = fun i => y₁ (b i) := funext fun i => (hb' i).symm
  have comb : ∀ (a : Fin (2 * P.g) → ℕ) (q : I), y₁ q = linComb lev.pt a → y₂ q = linComb (fun i => y₂ (b i)) a :=
    fun a q h => comb_eq (W := fun a b u => WeilIs P.A P.L (m ^ 2 : ℕ) a b u) cm hu hmul hnd t₁ t₂ s₂ hw b a q
      (by rw [h, eb]; rfl)
  have prim : ∀ {T : Type} [CommRing T] [Nontrivial T] (φ : K →+* T),
      IsPrimitiveRoot (Units.map φ.toMonoidHom ζ) (m ^ 2) := fun φ =>
    hζ.map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  obtain ⟨lev', hl'⟩ := GlobalTheory.exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp K) P (m ^ 2) (unitOn ζ) lev.prim
    (fun F _ s => by
      have : Nontrivial Γ(Spec (CommRingCat.of F), ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)⟩
      rw [← map_natCast (Spec.preimage s).hom]
      exact (map_ne_zero _).2 hK) (fun i => y₂ (b i)) (fun i => t₂ _)
    (fun i k => hw _ _ _ (by rw [hb', hb']; exact lev.pairing i k))
  choose q hq using fun a => s₁ _ (ThetaPtDet.levelPoint_pow lev rfl a)
  have e₁ : (fun a => y₁ (q a)) = GlobalTheory.levelPoint lev rfl := funext hq
  have e₂ : (fun a => y₂ (q a)) = GlobalTheory.levelPoint lev' rfl := funext fun a =>
    (comb _ _ (hq a)).trans (by rw [← hl']; rfl)
  have w₁ := ThetaDescentLevel.isThetaPt_reindex v₁ q
  have w₂ := ThetaDescentLevel.isThetaPt_reindex v₂ q
  rw [e₁] at w₁
  rw [e₂] at w₂
  obtain ⟨φ, ⟨hφ, t, ht⟩, hl⟩ := GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion.1 P.g n 2 j _ m hn ho le_rfl rfl hm hb K
    (Nat.cast_ne_zero.2 hn.ne_zero) P P rfl rfl _ lev lev' _ w₁ w₂
  have key : ∀ p, y₁ p ≫ φ.hom = y₂ p := fun p => by
    obtain ⟨d, hd⟩ := lev.span K (𝟙 _) (y₁ p) (t₁ p)
    have hd' : linComb lev.pt (fun i => (d i : ℕ)) = y₁ p :=
      (congrArg (linComb · _) (funext fun i => (Category.id_comp (lev.pt i)).symm)).trans hd
    rw [comb _ _ hd'.symm, ← hd', ThetaPtDet.linComb_comp, ← hl']
    exact congrArg (linComb · _) (funext hl)
  obtain ⟨w, hw'⟩ := LBIso.symm (⟨t, ht⟩ : LBIso _ _)
  have h3 : 3 ≤ n := by
    have := hn.two_le
    obtain ⟨c, rfl⟩ := ho
    omega
  have hid := MatchRigid.aut_eq_id hL P (𝟙 _) h3 (Nat.cast_ne_zero.2 hn.ne_zero) φ w hw' fun x hx => by
    have hd : n ∣ m ^ 2 := by
      rw [hm]
      exact dvd_pow (Dvd.dvd.mul_left (dvd_pow (dvd_pow_self n two_ne_zero) two_ne_zero) _) two_ne_zero
    obtain ⟨c, hc⟩ := hd
    obtain ⟨r, rfl⟩ := s₁ x (by rw [hc, pow_mul]; erw [hx]; exact one_pow _)
    exact (key r).trans (hfix r hx)
  rw [← key, hid, Category.comp_id]

theorem labels_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (n j m : ℕ), n.Prime → Odd n → m = n ^ j * (n ^ 2) ^ 2 → ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < m → ∀ (x₁ x₂ : QkPt D (Kb R) (m ^ 2) → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D A (m ^ 2) x₁ → LabTors D A (m ^ 2) x₂ → (∀ p, x₁ p ^ n = 1 → x₂ p = x₁ p) → ∀ v : QkPt D (Kb R) (m ^ 2) → Kb R, IsThetaPt A m x₁ (fun p => GlobalTheory.Ex.fnOf (v p)) → IsThetaPt A m x₂ (fun p => GlobalTheory.Ex.fnOf (v p)) → ∀ p, x₂ p = x₁ p := by
  intro R _ _ _ D A n j m hn ho hm hb x₁ x₂ ⟨s₁, t₁, _, _, w₁⟩ ⟨s₂, t₂, _, _, w₂⟩ hfix v v₁ v₂ p
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  obtain ⟨P, g, hg, hP, hmul, hs⟩ := hL.polBaseChange _ (Sp (Kb R)) (jFK (R := R) (Kb R)) A
  have hp : IsGrpPullback P.A A.A _ g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hmul]
    rfl⟩
  have hl : LBIso P.L (A.L.pull g) := LBIso.symm hs
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp (Kb R))) (jFK (R := R) (Kb R)) (Category.id_comp _).symm
  have hE : ∀ x, x.left = (e.symm x).left ≫ g := fun x =>
    (congrArg (fun z => z.left) (e.apply_symm_apply x).symm).trans (he _)
  have kW : ∀ (s : Sp (Kb R) ⟶ Sp (FractionRing R)) (_ : s = 𝟙 _ ≫ jFK (R := R) (Kb R))
      (x y : baseOver (Sp (Kb R)) ⟶ P.A) (x₀ y₀ : Over.mk s ⟶ A.A) (c : Γ(Sp (Kb R), ⊤)ˣ),
      x₀.left = x.left ≫ g → y₀.left = y.left ≫ g →
      (WeilIs P.A P.L (m ^ 2 : ℕ) x y c ↔ WeilIs A.A A.L (m ^ 2 : ℕ) x₀ y₀ c) := by
    rintro s rfl x y x₀ y₀ c hx hy
    have := P.isAb.comm
    exact weilIs_grpPullback_of_comm' _ _ _ _ _ g _ _ A.isLB P.isLB hp hl (baseOver _) _ x y x₀ y₀ c hx hy
  have kT : ∀ (s : Sp (Kb R) ⟶ Sp (FractionRing R)) (_ : s = 𝟙 _ ≫ jFK (R := R) (Kb R))
      (x : QkPt D (Kb R) (m ^ 2) → (baseOver (Sp (Kb R)) ⟶ P.A)) (x₀ : QkPt D (Kb R) (m ^ 2) → (Over.mk s ⟶ A.A))
      (u : QkPt D (Kb R) (m ^ 2) → Γ(Sp (Kb R), ⊤)), (∀ i, (x₀ i).left = (x i).left ≫ g) →
      (∀ i, x i ^ m ^ 2 = 1) → IsThetaPt A m x₀ u → IsThetaPt P m x u := by
    rintro s rfl x x₀ u hx ht h
    exact (ThetaPtUp.isThetaPt_iff (T := baseOver (Sp (Kb R))) hp hl hx ht _).2 h
  have tor : ∀ {k : ℕ} (x), x ^ k = 1 → e.symm x ^ k = 1 := fun x h => by rw [← map_pow, h, map_one]
  have tor' : ∀ {k : ℕ} (x), x ^ k = 1 → e x ^ k = 1 := fun x h => by rw [← map_pow, h, map_one]
  refine e.symm.injective (eq_of_isAlgClosed P hn ho hm (by rw [hP]; exact hb) (y₁ := fun p => e.symm (x₁ p))
    (y₂ := fun p => e.symm (x₂ p)) (fun p => tor _ (t₁ p)) (fun p => tor _ (t₂ p))
    (fun y hy => (s₁ _ (tor' y hy)).imp fun q h => (congrArg e.symm h).trans (e.symm_apply_apply y))
    (fun y hy => (s₂ _ (tor' y hy)).imp fun q h => (congrArg e.symm h).trans (e.symm_apply_apply y))
    (fun q q' c h => ?_) (fun q h => congrArg e.symm (hfix q ?_))
    (kT _ (Category.id_comp _).symm _ _ _ (fun i => hE _) (fun i => tor _ (t₁ i)) v₁)
    (kT _ (Category.id_comp _).symm _ _ _ (fun i => hE _) (fun i => tor _ (t₂ i)) v₂) p)
  · obtain ⟨z, rfl⟩ : ∃ z : (Kb R)ˣ, unitOn z = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (Kb R))).hom.hom.toMonoidHom c, Units.ext
        ((Scheme.ΓSpecIso (CommRingCat.of (Kb R))).commRingCatIsoToRingEquiv.symm_apply_apply c.val)⟩
    exact (kW _ (Category.id_comp _).symm _ _ _ _ _ (hE _) (hE _)).2 ((w₂ _ _ _).1 ((w₁ _ _ _).2
      ((kW _ (Category.id_comp _).symm _ _ _ _ _ (hE _) (hE _)).1 h)))
  · exact (congrArg (· ^ n) (e.apply_symm_apply _).symm).trans (tor' _ h)

end GlobalTheory.Mum.LabelRigid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsTraitCompatibleLevelsMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem GlobalTheory.Mum.lab_level_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A),
    OneTrait D.toPre A lab → ∀ k d : ℕ, 1 ≤ k → 1 ≤ d →
    ∀ (p : QkPt D.toPre (Kb R) k) (q : QkPt D.toPre (Kb R) (k * d)), q.y = d • p.y → q.g = p.g →
      lab (k * d) q = lab k p := by
  intro R _ _ _ _ D A lab hO k d hk hd p q hy hg
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, -, -, hG', ⟨ga, hga, hcart, -⟩, hc, hind⟩ := hO
  have := hW.1
  haveI : CharZero W := hW.2.2
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hG := GlobalTheory.globalFns_holds
  have hL := GlobalTheory.firstFiveLaws
  have hN1 : 1 ≤ k * d := Nat.mul_pos hk hd
  have hem : em.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb W) :=
    RingHom.ext em.commutes
  have hsq : spMap em.toRingHom ≫ jFK (R := R) (Kb R) = (TFK (R := W) (Kb W)).hom ≫ spMap ga := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hem]
    refine congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    simp only [RingHom.comp_apply]
    rw [hga r]
    exact hc r
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hcart (TFK (R := W) (Kb W)) _ hsq
  let s : Over.mk (spMap em.toRingHom ≫ jFK (R := R) (Kb R)) ⟶ TFK (R := R) (Kb R) :=
    Over.homMk (spMap em.toRingHom) rfl
  have hcomp : ∀ {m : ℕ} (r : QkPt D.toPre (Kb R) m), 1 ≤ m →
      QkToAkU U'.toUnifPre (Kb W) m (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem r))
        (e.symm (s ≫ lab m r)) := by
    intro m r hm
    refine hind m hm r _ _ _ ((GlobalTheory.TorusExt.qkExt_iff hB _ hem _ _).2 rfl) rfl
      ((GlobalTheory.ArcPull.eq_pullQk_iff hD hG hc hB hB' _ _).1 rfl).2 ?_
    rw [← he, e.apply_symm_apply]
    rfl
  have h₁ := hcomp p hk
  have h₂ := ((GlobalTheory.LevelCompat.qkToAkU_level hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k d (k * d) hk hd rfl
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem p))
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem q)) (e.symm (s ≫ lab (k * d) q))).1
    (by show hD.xe.symm q.y = d • hD.xe.symm p.y; rw [hy, map_nsmul])
    (by
      show GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem q.g) =
        GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem p.g)
      rw [hg])).2 (hcomp q hN1)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k hk
  have hx := ((hf _ _).1 h₂).trans ((hf _ _).1 h₁).symm
  have hs : s ≫ lab (k * d) q = s ≫ lab k p := e.symm.injective hx
  have : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  exact Over.OverMorphism.ext ((cancel_epi (spMap em.toRingHom)).1 (congrArg (fun z => z.left) hs))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem act_val_frac : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : D'.X) (y₀ : D₀.X) (g : GtPtF D' F) (g' : GtPtF D₀ F), GtPtF.IsIota y g → GtPtF.IsIota y₀ g' → Act D' D₀ pr h g g' → ∀ (χ : D₀.X) (u : LB.Gen (CmpLB D' D₀ pr (h χ) χ)), Nrm u → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → val (D₀.tau y₀ χ) (𝟙 _) z (rr J) = val (D'.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D'.c y)) z J := by
  intro R _ _ D₀ D' pr h F _ _ y y₀ g g' hg hg' ha χ u hu z J hJ
  have hsurj : Surjective (jFK (R := R) F) := GlobalTheory.Balanced.surjective_spMap _
  have hflat : Flat (jFK (R := R) F) := (inferInstance : Flat (spMap (algebraMap (FractionRing R) F)))
  have hb : g.b.left = jFK (R := R) F ≫ ptK (D'.c y) := by
    rw [hg.1]
    have e : toUnit (TF (R := R) F) = (Over.homMk (jFK (R := R) F) rfl : TF (R := R) F ⟶ TK R) ≫ toUnit (TK R) :=
      toUnit_unique _ _
    show (toUnit (TF (R := R) F) ≫ D'.c y).left = _
    rw [e, Category.assoc, Over.comp_left]
    rfl

  have step1 : ∀ (z' : (TF (R := R) F).left) (J' : _), Good (JN D' D₀) z' J' →
      val (D₀.tau y₀ χ) (jFK (R := R) F) z' (rr J') =
        val (D'.tau y (h χ)) (jFK (R := R) F) z' (rl J') * val u (jFK (R := R) F ≫ ptK (D'.c y)) z' J' := by
    intro z' J' hJ'
    have g₀ := (isPart_inr D'.P.L D₀.P.L).good hJ'
    have g₁ := (isPart_inl D'.P.L D₀.P.L).good hJ'
    have e := ha.2 χ u hu z' J' hJ'
    rw [val_corr g₀ (hg'.2 χ), val_corr g₁ (hg.2 (h χ)), val_pull g₀, val_pull g₁, hb] at e
    simp only [Category.id_comp] at e
    exact e

  have p₀ := isPart_inr D'.P.L D₀.P.L
  have p₁ := isPart_inl D'.P.L D₀.P.L
  let t₀ := p₀.gen (D₀.tau y₀ χ)
  let t₂ := LB.mulGen (JN D' D₀) _ _ _ _ (p₁.gen (D'.tau y (h χ))) (LB.pullGen (JN D' D₀) _ _ u (ptK (D'.c y)))
  have key := GlobalTheory.Balanced.val_descend (jn_isLB D' D₀) t₀ t₂ (jFK (R := R) F) (fun z' J' hJ' => by
    rw [p₀.val_gen _ _ _ hJ', val_mul hJ', p₁.val_gen _ _ _ hJ', val_pull hJ']
    exact step1 z' J' hJ') z J hJ
  rw [p₀.val_gen _ _ _ hJ, val_mul hJ, p₁.val_gen _ _ _ hJ, val_pull hJ, Category.id_comp] at key
  exact key

end GlobalTheory.Mum.Two

end
end

