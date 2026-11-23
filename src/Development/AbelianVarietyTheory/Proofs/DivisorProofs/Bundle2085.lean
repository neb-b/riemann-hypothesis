module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomAtIffOfSpecializes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.LevelClopen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem eSec_diag {A : Over S} [GrpObj A] :
    eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left = eSec A ≫ (lift (𝟙 A) (𝟙 A)).left := by
  simp only [eSec, ← Over.comp_left]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, Category.comp_id]
    rw [MonObj.comp_one]
    show toUnit _ ≫ η = η
    rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · simp

theorem exists_cub {b : Base D R} {s : S ⟶ Sp R} (o : Pre b s) :
    ∃ PP : RigLB o.A, PP.L = o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left ∧ Nonempty (CubicalStr o.A PP) := by
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  obtain ⟨t, ht⟩ := GlobalTheory.HkFam.cube_of_exists_relAmple o.ab hL o.ample hL
  have hR : Out.Rigidified o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) := by
    obtain ⟨t₁, ht₁⟩ := o.rig₁
    exact ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_pull_pull o.P (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left (eSec o.A) _
      (eSec o.A) eSec_diag ⟨pullGenLB t₁ (eSec o.A), pullGenLB_isGen ht₁ _⟩
  exact GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 S o.A o.ab _ hL hR ⟨t, ht⟩

theorem isUnit_base {b : Base D R} {s : S ⟶ Sp R} (n : ℕ) (hnp : n.Coprime p) : IsUnit (n : Γ(S, ⊤)) := by
  have := ((b.unit n hnp).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map s.appTop.hom
  simpa using this

theorem geomAt_transport {b : Base D R} {N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {s : S ⟶ Sp R}
    (o : PreEta b N s) (R' : Type) [CommRing R'] [HenselianLocalRing R']
    [IsAlgClosed (IsLocalRing.ResidueField R')] (t : Sp R' ⟶ S) {k k' : Type} [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] (i : Sp k ⟶ Sp R') (i' : Sp k' ⟶ Sp R') :
    o.GeomAt k (i ≫ t) → o.GeomAt k' (i' ≫ t) := by
  intro hT
  have hA := o.ab
  have hS : ∀ n : ℕ, 0 < n → n.Coprime p → IsUnit (n : Γ(S, ⊤)) :=
    fun n _ hnp => isUnit_base (b := b) (s := s) n hnp
  have hRu : ∀ n : ℕ, 0 < n → n.Coprime p → IsUnit (n : R') := by
    intro n hn hnp
    have := ((hS n hn hnp).map t.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom
    simpa using this
  obtain ⟨PP, hPP, ⟨cub⟩⟩ := exists_cub o.toPre
  unfold PreEta.GeomAt at hT ⊢
  change ∃ I : TateIsoO D k' (Over.mk (i' ≫ t) ⟶ o.A) _
      (fun n g g' z => Out.WeilIs o.A (o.toPre.P.pull (lift (𝟙 o.toPre.A) (𝟙 o.toPre.A)).left) n g g' (unitOn z)), _
  rw [← hPP]
  change ∃ I : TateIsoO D k (Over.mk (i ≫ t) ⟶ o.A) _
      (fun n g g' z => Out.WeilIs o.A (o.toPre.P.pull (lift (𝟙 o.toPre.A) (𝟙 o.toPre.A)).left) n g g' (unitOn z)), _ at hT
  rw [← hPP] at hT
  obtain ⟨φ, rfl⟩ : ∃ φ : R' →+* k, i = spMap φ := ⟨(Spec.preimage i).hom, by simp [spMap]⟩
  obtain ⟨φ', rfl⟩ : ∃ φ' : R' →+* k', i' = spMap φ' := ⟨(Spec.preimage i').hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := hT
  let A := o.A
  let lvR : D.La → (Over.mk t ⟶ A) := fun a => toUnit _ ≫ o.eta a
  let j : Over.mk (spMap φ ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ) rfl
  let j' : Over.mk (spMap φ' ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ') rfl
  have hj : ∀ a, toUnit (Over.mk (spMap φ ≫ t)) ≫ o.eta a = j ≫ lvR a := fun a => by
    simp only [lvR, ← Category.assoc]; congr 1
  have hj' : ∀ a, toUnit (Over.mk (spMap φ' ≫ t)) ≫ o.eta a = j' ≫ lvR a := fun a => by
    simp only [lvR, ← Category.assoc]; congr 1
  let ρ : (Over.mk t ⟶ A) →* (Over.mk (spMap φ ≫ t) ⟶ A) :=
    { toFun := fun g => j ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun g h => MonObj.comp_mul _ _ _ }
  let ρ' : (Over.mk t ⟶ A) →* (Over.mk (spMap φ' ≫ t) ⟶ A) :=
    { toFun := fun g => j' ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun g h => MonObj.comp_mul _ _ _ }
  have hpull : ∀ {K : Type} [Field K] (ψ : R' →+* K) (n : ℕ) (g h : Over.mk t ⟶ A) (u : R'ˣ),
      Out.WeilIs A PP.L (n : ℤ) g h (unitOn u) →
      Out.WeilIs A PP.L (n : ℤ) ((Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) ≫ g)
        ((Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) ≫ h)
        (unitOn (Units.map ψ.toMonoidHom u)) := by
    intro K _ ψ n g h u H
    have H' := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds hA PP.isLB
      (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) H
    have e : Units.map (spMap ψ).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map ψ.toMonoidHom u) :=
      Units.ext (congrArg (fun q => q.hom (u : R')) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))).symm
    exact e ▸ H'
  have hetapow : ∀ a, o.eta a ^ N = 1 := by
    intro a
    have : ∀ m : ℕ, o.eta (m • a) = o.eta a ^ m := by
      intro m
      induction m with
      | zero =>
        have h0 := o.eta_add 0 0
        rw [add_zero] at h0
        rw [zero_smul, pow_zero]
        exact left_eq_mul.1 h0 |>.symm ▸ rfl
      | succ m ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]
    rw [← this]; exact o.eta_ker a
  have hpow : ∀ a, lvR a ^ N = 1 := fun a => by
    simp only [lvR]; rw [← MonObj.comp_pow, hetapow, MonObj.comp_one]
  have h1 : ∀ n, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k φ).1
  have h2 : ∀ n, 0 < n → n.Coprime p → ∀ x : Over.mk (spMap φ ≫ t) ⟶ A, x ^ n = 1 →
      ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧ ρ g = x :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k φ).2
  have h3 : ∀ n, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 → ρ' g = ρ' h → g = h :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k' φ').1
  have h4 : ∀ n, 0 < n → n.Coprime p → ∀ x : Over.mk (spMap φ' ≫ t) ⟶ A, x ^ n = 1 →
      ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧ ρ' g = x :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k' φ').2
  have h5 := fun n (hn : 0 < n) (hnp : n.Coprime p) =>
    (GlobalTheory.rootsOfUnity_map_bijective_of_henselian R' k φ n hn (hRu n hn hnp))
  have h6 := fun n (hn : 0 < n) (hnp : n.Coprime p) =>
    (GlobalTheory.rootsOfUnity_map_bijective_of_henselian R' k' φ' n hn (hRu n hn hnp))
  have h7 : ∀ (c : D.O) (g h : Over.mk t ⟶ A), (g * h) ≫ o.act.act c = (g ≫ o.act.act c) * (h ≫ o.act.act c) := by
    intro c g h
    haveI := o.act.hom c
    exact MonObj.mul_comp _ _ _
  have h8 : ∀ c, (1 : Over.mk (spMap φ' ≫ t) ⟶ A) ≫ o.act.act c = 1 := by
    intro c
    haveI := o.act.hom c
    exact MonObj.one_comp _
  have h9 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 →
      ∃ u : R'ˣ, u ^ n = 1 ∧ Out.WeilIs A PP.L (n : ℤ) (ρ g) (ρ h) (unitOn (Units.map φ.toMonoidHom u)) ∧
        Out.WeilIs A PP.L (n : ℤ) (ρ' g) (ρ' h) (unitOn (Units.map φ'.toMonoidHom u)) := by
    intro n hn hnp g h hg hh
    have loc : ∀ z : Over.mk t ⟶ A, z ^ n = 1 → ∀ p : (Over.mk t).left,
        ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
          ∃ θ : Out.ThetaGrp A PP.L (n : ℤ) (Out.overRes V), θ.pt = Out.overResι V ≫ z := by
      intro z hz p
      obtain ⟨θ, hθ⟩ := GlobalTheory.TorsionThetaLocal.exists_theta_of_pow_eq_one S A PP cub R' t n z hz
      obtain ⟨θ', hθ'⟩ := GlobalTheory.CommutatorPairing.exists_pull PP.isLB θ (Out.overResι ⊤)
      exact ⟨⊤, trivial, θ', by rw [hθ', hθ]⟩
    obtain ⟨c, hc⟩ := GlobalTheory.CommutatorPairing.exists_weilIs GlobalTheory.globalFns_holds hA PP.isLB (loc g hg) (loc h hh)
    have pw : ∀ m : ℕ, Out.WeilIs A PP.L (n : ℤ) (g ^ (m + 1)) h (c ^ (m + 1)) := by
      intro m
      induction m with
      | zero => simpa using hc
      | succ m ih =>
        rw [pow_succ g (m + 1), pow_succ c (m + 1)]
        exact GlobalTheory.DiagPairing.weilIs_mul_left GlobalTheory.globalFns_holds hA PP.isLB ih hc
    have e := pw n
    rw [pow_succ g, hg, _root_.one_mul] at e
    have hcn := GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds hA PP.isLB e hc
    rw [pow_succ, mul_eq_right] at hcn
    obtain ⟨u, rfl⟩ : ∃ u : R'ˣ, unitOn u = c :=
      (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R')).symm.commRingCatIsoToRingEquiv.toMulEquiv).surjective c
    have hu : u ^ n = 1 := by
      apply unitOn_injective_of_commRing
      show unitOn (u ^ n) = unitOn 1
      rw [unitOn, unitOn, map_pow, map_one]
      exact hcn
    have H := hc
    exact ⟨u, hu, hpull φ n g h u H, hpull φ' n g h u H⟩
  have h10 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ (x y : Over.mk (spMap φ ≫ t) ⟶ A) (c c' : kˣ),
      Out.WeilIs A PP.L (n : ℤ) x y (unitOn c) → Out.WeilIs A PP.L (n : ℤ) x y (unitOn c') → c = c' :=
    fun n _ _ x y c c' h h' => GlobalTheory.weilIs_unique_fieldPoint S A PP.L PP.isLB k (spMap φ ≫ t) n x y c c' h h'
  obtain ⟨I', hI'⟩ := GlobalTheory.UPel.HT.TateTransportO.transport_alg D (R := R') (k := k) (k' := k')
    (QR := Over.mk t ⟶ A) (Q := Over.mk (spMap φ ≫ t) ⟶ A) (Q' := Over.mk (spMap φ' ≫ t) ⟶ A)
    (fun a b => mul_comm a b) (fun c g => g ≫ o.act.act c) (fun c g => g ≫ o.act.act c)
    (fun c g => g ≫ o.act.act c)
    (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c)) (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c))
    ρ ρ' (Units.map φ.toMonoidHom) (Units.map φ'.toMonoidHom)
    h1 h2 h3 h4 (fun n hn hnp => (h5 n hn hnp).1) (fun n hn hnp => (h5 n hn hnp).2)
    (fun n hn hnp => (h6 n hn hnp).1)
    h7 (fun c g => (Category.assoc j g (o.act.act c)).symm) (fun c g => (Category.assoc j' g (o.act.act c)).symm)
    h8 h9 h10 I
  exact ⟨I', fun a => (hj' a).trans (hI' N hN hNp a (lvR a) (hpow a) ((hj a).symm.trans (hI a)))⟩

theorem geomAt_iff_of_specializes {b : Base D R} {N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {s : S ⟶ Sp R}
    (o : PreEta b N s) {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    (x : Sp k ⟶ S) (x' : Sp k' ⟶ S) (u : Sp k) (u' : Sp k') (h : x'.base u' ⤳ x.base u) :
    o.GeomAt k x ↔ o.GeomAt k' x' := by
  obtain ⟨R', _, _, _, r, i, i', rfl, rfl⟩ := GlobalTheory.geomPoints_factor_henselian_of_specializes x x' u u' h
  exact ⟨geomAt_transport hN hNp o R' r i i', geomAt_transport hN hNp o R' r i' i⟩

end GlobalTheory.UPel.HT.LevelClopen

namespace GlobalTheory.UPel.HT

open LevelClopen

theorem PreEta.exists_clopen_geomAt : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R)
    (o : PreEta b N s), ∃ U : S.Opens, IsClosed (U : Set S) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S), (Set.range x.base ⊆ (U : Set S) ↔ o.GeomAt k x) := by
  intro p _ D R _ b N hN3 hNp S _ s o
  have hN : 0 < N := by omega
  let U : Set S := {z | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ S),
    z ∈ Set.range x.base ∧ o.GeomAt k x}
  have hclo : IsClopen U := by
    refine GlobalTheory.SpecGenClopen.isClopen_of_specializes_iff S U fun z w hzw => ?_
    constructor
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := GlobalTheory.FinEt.exists_algClosed_point S w
      obtain ⟨u', hu'⟩ : w ∈ Set.range x'.base := by rw [show Set.range x'.base = {w} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩,
        (geomAt_iff_of_specializes hN hNp o x' x u' u ?_).2 hG⟩
      rw [hu, hu']
      exact hzw
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := GlobalTheory.FinEt.exists_algClosed_point S z
      obtain ⟨u', hu'⟩ : z ∈ Set.range x'.base := by rw [show Set.range x'.base = {z} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩,
        (geomAt_iff_of_specializes hN hNp o x x' u u' ?_).1 hG⟩
      rw [hu, hu']
      exact hzw
  refine ⟨⟨U, hclo.isOpen⟩, hclo.isClosed, fun k _ _ x => ⟨fun hx => ?_,
    fun hG z hz => ⟨k, inferInstance, inferInstance, x, hz, hG⟩⟩⟩
  let pt : Sp k := (⊥ : PrimeSpectrum k)
  obtain ⟨k', _, _, x', ⟨u', hu'⟩, hG'⟩ := hx ⟨pt, rfl⟩
  exact (geomAt_iff_of_specializes hN hNp o x x' pt u' (hu' ▸ specializes_rfl)).2 hG'

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsAreConstantAbelianSchemeNoetheria
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

open Opposite TopologicalSpace

theorem const_of_isAbelianScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → Const A.hom := by
  intro R _ _ A _ hA
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  haveI : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth A.hom
  have hbij := ((GlobalTheory.ProperFunctions.functions_of_isProper).2.2 R A.left A.hom).1
  intro g hg
  have hc : ∀ (U V : A.left.affineOpens) (h : V.1 ≤ U.1),
      A.left.presheaf.map (homOfLE h).op (g (op U)) = g (op V) := by
    intro U V h
    have e := congrFun (congrFun (congrFun hg (op U)) (op V)) (homOfLE h).op
    exact (sub_eq_zero.1 e).symm
  obtain ⟨t, ht, -⟩ := A.left.sheaf.existsUnique_gluing' (fun U : A.left.affineOpens ↦ U.1) ⊤
    (fun _ ↦ homOfLE le_top) (iSup_affineOpens_eq_top A.left).ge (fun U ↦ g (op U)) (by
      intro U V
      refine A.left.sheaf.eq_of_locally_eq' (fun W : {W : A.left.affineOpens // W.1 ≤ U.1 ⊓ V.1} ↦ W.1.1)
        (U.1 ⊓ V.1) (fun W ↦ homOfLE W.2) ?_ _ _ fun W ↦ ?_
      · intro x hx
        obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens hx
        exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWUV⟩, hxW⟩
      · dsimp only
        have e : ∀ {a b c : Opens A.left} (f : b ⟶ a) (f' : c ⟶ b) (x : Γ(A.left, a)),
            A.left.presheaf.map f'.op (A.left.presheaf.map f.op x) = A.left.presheaf.map (f' ≫ f).op x := by
          intros; simp
        refine (e _ _ _).trans ((hc U W.1 (W.2.trans inf_le_left)).trans
          ((hc V W.1 (W.2.trans inf_le_right)).symm.trans (e _ _ _).symm)))
  obtain ⟨r, hr⟩ := hbij.2 t
  refine ⟨r, fun U ↦ ?_⟩
  rw [← ht U.unop, ← hr]
  rfl

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawGlueOverCoprodBase
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdGlue

variable {T T₁ : Scheme.{0}}

theorem isPb (Y : Over T) : IsPullback (fst Y Y).left (snd Y Y).left Y.hom Y.hom :=
  IsPullback.of_hasPullback Y.hom Y.hom

theorem tens_hom (Y : Over T) : (Y ⊗ Y).hom = (fst Y Y).left ≫ Y.hom := (Over.w (fst Y Y)).symm

noncomputable def incl (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : (Y₁ ⊗ Y₁).left ⟶ (Y ⊗ Y).left :=
  (isPb Y).lift ((fst Y₁ Y₁).left ≫ j) ((snd Y₁ Y₁).left ≫ j) (by
    rw [Category.assoc, Category.assoc, w, ← Category.assoc, ← Category.assoc, (isPb Y₁).w])

@[reassoc (attr := simp)] theorem incl_fst (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : incl v Y Y₁ j w ≫ (fst Y Y).left = (fst Y₁ Y₁).left ≫ j :=
  (isPb Y).lift_fst _ _ _

@[reassoc (attr := simp)] theorem incl_snd (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : incl v Y Y₁ j w ≫ (snd Y Y).left = (snd Y₁ Y₁).left ≫ j :=
  (isPb Y).lift_snd _ _ _

theorem incl_pullback (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (h : IsPullback j Y₁.hom Y.hom v) :
    IsPullback (incl v Y Y₁ j h.w) (Y₁ ⊗ Y₁).hom (Y ⊗ Y).hom v := by
  have w : incl v Y Y₁ j h.w ≫ (Y ⊗ Y).hom = (Y₁ ⊗ Y₁).hom ≫ v := by
    rw [tens_hom, tens_hom, incl_fst_assoc, h.w, Category.assoc]
  have e1 : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, (s.fst ≫ (fst Y Y).left) ≫ Y.hom = s.snd ≫ v := fun s => by
    rw [Category.assoc, ← tens_hom, s.condition]
  have e2 : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, (s.fst ≫ (snd Y Y).left) ≫ Y.hom = s.snd ≫ v := fun s => by
    rw [Category.assoc, ← (isPb Y).w, ← tens_hom, s.condition]
  let lf : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, s.pt ⟶ (Y₁ ⊗ Y₁).left := fun s =>
    (isPb Y₁).lift (h.lift (s.fst ≫ (fst Y Y).left) s.snd (e1 s)) (h.lift (s.fst ≫ (snd Y Y).left) s.snd (e2 s))
      (by rw [h.lift_snd, h.lift_snd])
  have lf1 : ∀ s, lf s ≫ (fst Y₁ Y₁).left = h.lift (s.fst ≫ (fst Y Y).left) s.snd (e1 s) :=
    fun s => (isPb Y₁).lift_fst _ _ _
  have lf2 : ∀ s, lf s ≫ (snd Y₁ Y₁).left = h.lift (s.fst ≫ (snd Y Y).left) s.snd (e2 s) :=
    fun s => (isPb Y₁).lift_snd _ _ _
  refine ⟨⟨w⟩, ⟨Limits.PullbackCone.IsLimit.mk w lf ?_ ?_ ?_⟩⟩
  · intro s
    apply (isPb Y).hom_ext
    · rw [Category.assoc, incl_fst, reassoc_of% (lf1 s), h.lift_fst]
    · rw [Category.assoc, incl_snd, reassoc_of% (lf2 s), h.lift_fst]
  · intro s
    rw [tens_hom Y₁, reassoc_of% (lf1 s), h.lift_snd]
  · intro s m hm1 hm2
    rw [tens_hom Y₁] at hm2
    apply (isPb Y₁).hom_ext
    · rw [lf1]
      apply h.hom_ext
      · rw [h.lift_fst, Category.assoc, ← incl_fst v Y Y₁ j h.w, reassoc_of% hm1]
      · rw [h.lift_snd]; simpa only [Category.assoc] using hm2
    · rw [lf2]
      apply h.hom_ext
      · rw [h.lift_fst, Category.assoc, ← incl_snd v Y Y₁ j h.w, reassoc_of% hm1]
      · rw [h.lift_snd, ← hm2, Category.assoc, (isPb Y₁).w]

theorem incl_mul (f : T₁ ⟶ T) (A : Over T) [GrpObj A] (B : Over T₁) [GrpObj B] (φ : B.left ⟶ A.left)
    (h : IsGrpPullback B A f φ) : incl f A B φ h.1.w ≫ (μ[A]).left = (μ[B]).left ≫ φ := by
  let x₀ : Over.mk ((B ⊗ B).hom ≫ f) ⟶ A := Over.homMk ((fst B B).left ≫ φ) (by
    show _ = (B ⊗ B).hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  let y₀ : Over.mk ((B ⊗ B).hom ≫ f) ⟶ A := Over.homMk ((snd B B).left ≫ φ) (by
    show _ = (B ⊗ B).hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, ← (isPb B).w, Over.w])
  have hm := h.2 (B ⊗ B) (fst B B) (snd B B) x₀ y₀ rfl rfl
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at hm
  have e : incl f A B φ h.1.w = (lift x₀ y₀).left := by
    apply (isPb A).hom_ext
    · rw [incl_fst, ← Over.comp_left, lift_fst]; rfl
    · rw [incl_snd, ← Over.comp_left, lift_snd]; rfl
  rw [e]; exact hm

theorem colim_of_pullbacks {T T₁ T₂ : Scheme.{0}} (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T)
    (hT : Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) (Y : Over T) (Y₁ : Over T₁) (Y₂ : Over T₂)
    (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left)
    (h₁ : IsPullback j₁ Y₁.hom Y.hom v₁) (h₂ : IsPullback j₂ Y₂.hom Y.hom v₂) :
    Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (incl v₁ Y Y₁ j₁ h₁.w) (incl v₂ Y Y₂ j₂ h₂.w))) := by
  refine (((BinaryCofan.isVanKampen_iff _).1 (FinitaryExtensive.vanKampen _ hT)
    (Limits.BinaryCofan.mk (incl v₁ Y Y₁ j₁ h₁.w) (incl v₂ Y Y₂ j₂ h₂.w)) (Y₁ ⊗ Y₁).hom (Y₂ ⊗ Y₂).hom (Y ⊗ Y).hom
    ?_ ?_).2 ⟨incl_pullback v₁ Y Y₁ j₁ h₁, incl_pullback v₂ Y Y₂ j₂ h₂⟩)
  · exact (incl_pullback v₁ Y Y₁ j₁ h₁).w.symm
  · exact (incl_pullback v₂ Y Y₂ j₂ h₂).w.symm

end GlobalTheory.ProdGlue

open GlobalTheory.ProdGlue in
theorem GlobalTheory.ProdGlue.mul_glue : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂) (A₁ : Over S₁) [GrpObj A₁] (A₂ : Over S₂) [GrpObj A₂] (B₁ : Over T₁) [GrpObj B₁] (B₂ : Over T₂) [GrpObj B₂] (A₀ : Over T) [GrpObj A₀] (i₁ : B₁.left ⟶ A₁.left) (i₂ : B₂.left ⟶ A₂.left) (j₁ : B₁.left ⟶ A₀.left) (j₂ : B₂.left ⟶ A₀.left), IsGrpPullback B₁ A₁ f₁ i₁ → IsGrpPullback B₂ A₂ f₂ i₂ → IsGrpPullback B₁ A₀ v₁ j₁ → IsGrpPullback B₂ A₀ v₂ j₂ → ∀ (i : A₀.left ⟶ A₁.left ⨿ A₂.left), j₁ ≫ i = i₁ ≫ Limits.coprod.inl → j₂ ≫ i = i₂ ≫ Limits.coprod.inr → ∃ m : Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⟶ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)), ∀ l : (A₀ ⊗ A₀).left ⟶ (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))).left, l ≫ (fst (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (fst A₀ A₀).left ≫ i → l ≫ (snd (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (snd A₀ A₀).left ≫ i → l ≫ m.left = (μ[A₀]).left ≫ i := by

  intro S S₁ S₂ T T₁ T₂ u₁ u₂ ⟨hS⟩ v₁ v₂ ⟨hT⟩ f₁ f₂ A₁ _ A₂ _ B₁ _ B₂ _ A₀ _ i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ i ei₁ ei₂
  set X := Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) with hX
  have hV := (BinaryCofan.isVanKampen_iff _).1 (FinitaryExtensive.vanKampen _ hS)
    (Limits.BinaryCofan.mk (Limits.coprod.inl : A₁.left ⟶ A₁.left ⨿ A₂.left) Limits.coprod.inr) A₁.hom A₂.hom X.hom
    (Limits.coprod.inl_desc _ _).symm (Limits.coprod.inr_desc _ _).symm
  have pX : _ := hV.1 ⟨Limits.coprodIsCoprod _ _⟩
  have pX₁ : IsPullback (Limits.coprod.inl : A₁.left ⟶ A₁.left ⨿ A₂.left) A₁.hom X.hom u₁ := pX.1
  have pX₂ : IsPullback (Limits.coprod.inr : A₂.left ⟶ A₁.left ⨿ A₂.left) A₂.hom X.hom u₂ := pX.2
  obtain ⟨cX⟩ := colim_of_pullbacks u₁ u₂ hS X A₁ A₂ _ _ pX₁ pX₂
  obtain ⟨c0⟩ := colim_of_pullbacks v₁ v₂ hT A₀ B₁ B₂ _ _ hj₁.1 hj₂.1
  have D := Limits.BinaryCofan.IsColimit.desc' cX
    ((μ[A₁]).left ≫ Limits.coprod.inl) ((μ[A₂]).left ≫ Limits.coprod.inr)
  let ml : (X ⊗ X).left ⟶ X.left := D.1
  have hm₁ : incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ ml = (μ[A₁]).left ≫ Limits.coprod.inl := D.2.1
  have hm₂ : incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ ml = (μ[A₂]).left ≫ Limits.coprod.inr := D.2.2
  have hw : ml ≫ X.hom = (X ⊗ X).hom := by
    apply Limits.BinaryCofan.IsColimit.hom_ext cX
    · change incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ ml ≫ X.hom = incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ (X ⊗ X).hom
      rw [← Category.assoc, hm₁, Category.assoc, tens_hom, incl_fst_assoc]
      simp only [X, Over.mk_hom, Limits.coprod.inl_desc]
      rw [← Category.assoc, Over.w, ← Category.assoc, Over.w]
    · change incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ ml ≫ X.hom = incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ (X ⊗ X).hom
      rw [← Category.assoc, hm₂, Category.assoc, tens_hom, incl_fst_assoc]
      simp only [X, Over.mk_hom, Limits.coprod.inr_desc]
      rw [← Category.assoc, Over.w, ← Category.assoc, Over.w]
  refine ⟨Over.homMk ml hw, fun l hl₁ hl₂ => ?_⟩
  change l ≫ ml = _
  have key : ∀ {Tk Sk : Scheme.{0}} (vk : Tk ⟶ T) (uk : Sk ⟶ S) (fk : Tk ⟶ Sk) (Ak : Over Sk) [GrpObj Ak]
      (Bk : Over Tk) [GrpObj Bk] (ik : Bk.left ⟶ Ak.left) (jk : Bk.left ⟶ A₀.left) (ink : Ak.left ⟶ X.left)
      (hik : IsGrpPullback Bk Ak fk ik) (hjk : IsGrpPullback Bk A₀ vk jk) (eik : jk ≫ i = ik ≫ ink)
      (κ : (Ak ⊗ Ak).left ⟶ (X ⊗ X).left)
      (κf : κ ≫ (fst X X).left = (fst Ak Ak).left ≫ ink) (κs : κ ≫ (snd X X).left = (snd Ak Ak).left ≫ ink)
      (hmk : κ ≫ ml = (μ[Ak]).left ≫ ink),
      incl vk A₀ Bk jk hjk.1.w ≫ l ≫ ml = incl vk A₀ Bk jk hjk.1.w ≫ (μ[A₀]).left ≫ i := by
    intro Tk Sk vk uk fk Ak _ Bk _ ik jk ink hik hjk eik κ κf κs hmk
    have e : incl vk A₀ Bk jk hjk.1.w ≫ l = incl fk Ak Bk ik hik.1.w ≫ κ := by
      apply (isPb X).hom_ext
      · rw [Category.assoc, hl₁, incl_fst_assoc, eik, Category.assoc, κf, incl_fst_assoc]
      · rw [Category.assoc, hl₂, incl_snd_assoc, eik, Category.assoc, κs, incl_snd_assoc]
    rw [reassoc_of% e, hmk, reassoc_of% (incl_mul fk Ak Bk ik hik), reassoc_of% (incl_mul vk A₀ Bk jk hjk), eik]
  apply Limits.BinaryCofan.IsColimit.hom_ext c0
  · exact key v₁ u₁ f₁ A₁ B₁ i₁ j₁ _ hi₁ hj₁ ei₁ _ (incl_fst _ _ _ _ _) (incl_snd _ _ _ _ _) hm₁
  · exact key v₂ u₂ f₂ A₂ B₂ i₂ j₂ _ hi₂ hj₂ ei₂ _ (incl_fst _ _ _ _ _) (incl_snd _ _ _ _ _) hm₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpUnitsAndInversesAgreeOfLawsAgree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem hom_ext_of_cartesian {S S₀ X : Scheme.{0}} {q : X ⟶ S} {s₀ : S₀ ⟶ S} {A : Over S₀}
    {i : A.left ⟶ X} (h : IsPullback i A.hom q s₀) {T : Scheme.{0}} {t₀ : T ⟶ S₀}
    (c c' : Over.mk t₀ ⟶ A) (hc : c.left ≫ i = c'.left ≫ i) : c = c' := by
  apply Over.OverMorphism.ext
  apply h.hom_ext hc
  rw [Over.w c, Over.w c']

theorem oneAgree_invAgree_of_mulAgree : ∀ (S S₀ S₁ X : Scheme.{0}) (q : X ⟶ S) (s₀ : S₀ ⟶ S) (s₁ : S₁ ⟶ S) (A : Over S₀) [GrpObj A] (G : Over S₁) [GrpObj G] (i : A.left ⟶ X) (e : G.left ⟶ X), IsPullback i A.hom q s₀ → e ≫ q = G.hom ≫ s₁ → MulAgree G A e i → OneAgree s₁ s₀ G A e i ∧ ∀ (T : Scheme.{0}) (t₁ : T ⟶ S₁) (t₀ : T ⟶ S₀) (a : Over.mk t₁ ⟶ G) (a' : Over.mk t₀ ⟶ A), a.left ≫ e = a'.left ≫ i → (a⁻¹).left ≫ e = (a'⁻¹).left ≫ i := by
  intro S S₀ S₁ X q s₀ s₁ A _ G _ i e h he hm
  have one : OneAgree s₁ s₀ G A e i := by
    intro T t₁ t₀ ht
    have hw : ((1 : Over.mk t₁ ⟶ G).left ≫ e) ≫ q = t₀ ≫ s₀ := by
      rw [Category.assoc, he, ← Category.assoc, Over.w]; exact ht
    let a' : Over.mk t₀ ⟶ A := Over.homMk (h.lift _ t₀ hw) (by simp)
    have ha' : a'.left ≫ i = (1 : Over.mk t₁ ⟶ G).left ≫ e := h.lift_fst _ _ _
    have hmm := hm T t₁ t₀ 1 1 a' a' ha'.symm ha'.symm
    rw [_root_.mul_one] at hmm
    have h2 : a' * a' = a' := hom_ext_of_cartesian h _ _ (by rw [← hmm, ha'])
    have h3 : a' = 1 := by simpa using h2
    rw [← ha', h3]
  refine ⟨one, ?_⟩
  intro T t₁ t₀ a a' haa
  have ht : t₁ ≫ s₁ = t₀ ≫ s₀ := by
    have w1 : a.left ≫ G.hom = t₁ := Over.w a
    have w0 : a'.left ≫ A.hom = t₀ := Over.w a'
    calc t₁ ≫ s₁ = (a.left ≫ G.hom) ≫ s₁ := by rw [w1]
      _ = (a.left ≫ e) ≫ q := by rw [Category.assoc, Category.assoc, he]
      _ = (a'.left ≫ i) ≫ q := by rw [haa]
      _ = (a'.left ≫ A.hom) ≫ s₀ := by rw [Category.assoc, Category.assoc, h.w]
      _ = t₀ ≫ s₀ := by rw [w0]
  have hw : ((a⁻¹).left ≫ e) ≫ q = t₀ ≫ s₀ := by
    rw [Category.assoc, he, ← Category.assoc, Over.w]; exact ht
  let b' : Over.mk t₀ ⟶ A := Over.homMk (h.lift _ t₀ hw) (by simp)
  have hb' : b'.left ≫ i = (a⁻¹).left ≫ e := h.lift_fst _ _ _
  have hmm := hm T t₁ t₀ a a⁻¹ a' b' haa hb'.symm
  rw [_root_.mul_inv_cancel] at hmm
  have h2 : a' * b' = 1 := hom_ext_of_cartesian h _ _ (by rw [← hmm, one T t₁ t₀ ht])
  have h3 : b' = a'⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [← h3, hb']

end GlobalTheory.Desc
end

