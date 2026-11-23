module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0239
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveRootHodgeCpt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTorsionNoetherianChart
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Idemp

theorem sec_eq {A F : Type} [CommRing A] [Field F] (pq : A →+* F) (sc : F →+ A)
    (h1 : ∀ a, pq (sc a) = a) (h2 : ∀ u a, pq u = 0 → u * sc a = 0) (x : A) : sc (pq x) = sc 1 * x := by
  have a1 := h2 (sc 1 - 1) (pq x) (by simp [h1])
  have a2 := h2 (x - sc (pq x)) 1 (by simp [h1])
  linear_combination (-1 : A) * a1 - a2

theorem p_ne_zero {E : Type} [Field E] [NumberField E] {p : ℕ} {F : Type} [Field F]
    (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}))
    (h : IsSec pq sc) : p ≠ 0 := by
  intro hp
  have hbot : Ideal.span {(p : 𝓞 E)} = ⊥ := by simp [hp]
  haveI : (Ideal.span {(p : 𝓞 E)}).IsPrime := by rw [hbot]; exact Ideal.isPrime_bot
  have hinj : Function.Injective pq := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    rcases mul_eq_zero.1 (h.2 u 1 hu) with h0 | h0
    · exact h0
    · have := h.1 1
      rw [h0, map_zero] at this
      exact absurd this zero_ne_one
  have hf : IsField (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) :=
    (RingEquiv.ofBijective pq ⟨hinj, fun a => ⟨sc a, h.1 a⟩⟩).toMulEquiv.isField (Field.toIsField F)
  have hm : (Ideal.span {(p : 𝓞 E)}).IsMaximal := Ideal.Quotient.maximal_of_isField _ hf
  rw [hbot] at hm
  exact Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E) rfl

theorem finite_tors {E : Type} [Field E] [NumberField E] (N : ℕ) {p : ℕ} (hp : p ≠ 0) : Finite (TorsT E N p) := by
  haveI : Finite (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hp)
  infer_instance

theorem frac_epi {Ω : Type} [Field Ω] {O : Type} [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω)
    [IsFractionRing R Ω] : IsIso (spMap (fracToField R)) := by
  have hb : Function.Bijective (fracToField R) := by
    refine ⟨(fracToField R).injective, fun z => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    refine ⟨algebraMap R _ a / algebraMap R _ b, ?_⟩
    have hl : ∀ r : R, fracToField R (algebraMap R (FractionRing R) r) = algebraMap R Ω r := fun r =>
      IsFractionRing.lift_algebraMap (g := algebraMap R Ω) Subtype.val_injective r
    rw [map_div₀, hl, hl]
  haveI : IsIso (CommRingCat.ofHom (fracToField R)) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  exact inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (fracToField R))))

def mulT {E : Type} [Field E] [NumberField E] (N p : ℕ) (e : 𝓞 E) : TorsT E N p →* TorsT E N p :=
  AddMonoidHom.toMultiplicative
    { toFun := fun x i => Ideal.Quotient.mk _ e * x i
      map_zero' := by ext i; simp
      map_add' := fun a b => by ext i; simp [mul_add] }

theorem mulT_qmk {E : Type} [Field E] [NumberField E] (N p : ℕ) (e : 𝓞 E) (x : Fin N → 𝓞 E) :
    mulT N p e (qmk p x) = qmk p (e • x) := rfl

theorem qmk_surj {E : Type} [Field E] [NumberField E] (N p : ℕ) (t : TorsT E N p) : ∃ x, qmk p x = t := by
  choose x hx using fun i => Ideal.Quotient.mk_surjective (Multiplicative.toAdd t i)
  exact ⟨x, congrArg Multiplicative.ofAdd (funext hx)⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Idemp

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx


open Idemp in
theorem btOrder_stable_of_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) (G : GenTors 𝔐 p) (O : Type) [CommRing O] [Algebra O Ω] (c' : ∀ k, J k) [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω] (P : ChartPack G O c') (F : Type) [Field F] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})), Function.Surjective pq → IsSec pq sc → ∀ a ∈ P.Γ₁.btOrder ⊤, (fun t => a (toN sc (fromN pq t))) ∈ P.Γ₁.btOrder ⊤ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J _ y 𝔐 p G O _ _ c' _ _ _ P F _ pq sc _ hsec f hf
  haveI := finite_tors (E := E) (D.p + D.q) (p_ne_zero pq sc hsec)
  obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective (sc 1)
  have hα : ∀ t : TorsT E (D.p + D.q) p, toN sc (fromN pq t) = mulT _ p e t := by
    intro t
    refine congrArg Multiplicative.ofAdd (funext fun i => ?_)
    change sc (pq (Multiplicative.toAdd t i)) = Ideal.Quotient.mk _ e * Multiplicative.toAdd t i
    rw [he]
    exact sec_eq pq sc hsec.1 hsec.2 _
  haveI := 𝔐.t.act.hom e
  haveI := frac_epi (CR O y c')
  have h4 := (_root_.GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁
    𝔐.t.semi.smooth).2.2.2.1 (𝔐.t.act.act e) (mulT _ p e) (by
      intro t
      obtain ⟨x, rfl⟩ := qmk_surj _ p t
      rw [← cancel_epi (spMap (fracToField (CR O y c'))), ← P.pts₁, mulT_qmk, G.t₁.lin, Over.comp_left, P.pts₁]
      simp only [Category.assoc]) f hf
  simpa only [hα] using h4

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HFlag

section Lemmas

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']

theorem exists_forms_eq {n : ℕ} {b : Fin n → Module.Dual Ω V} (hb : LinearIndependent Ω b) (l : Fin n) :
    ∃ u : V, ∀ k, b k u = if k = l then 1 else 0 := by
  classical
  have hs : Function.Surjective (LinearMap.pi b : V →ₗ[Ω] (Fin n → Ω)) := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro φ hφ
    have hc : ∑ k, φ (Pi.single k 1) • b k = 0 := by
      ext u
      have h1 := LinearMap.congr_fun hφ u
      have h2 : (LinearMap.pi b : V →ₗ[Ω] (Fin n → Ω)) u = ∑ k, b k u • (Pi.single k 1 : Fin n → Ω) := by
        ext m
        simp [Finset.sum_apply, Pi.single_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LinearMap.dualMap_apply, h2, map_sum] at h1
      simpa [mul_comm] using h1
    have h0 := Fintype.linearIndependent_iff.1 hb _ hc
    refine LinearMap.pi_ext fun k x => ?_
    have : (Pi.single k x : Fin n → Ω) = x • (Pi.single k 1 : Fin n → Ω) := by
      ext m
      simp [Pi.single_apply]
    rw [this, map_smul, h0 k]
    simp
  obtain ⟨u, hu⟩ := hs (Pi.single l 1)
  refine ⟨u, fun k => ?_⟩
  have := congrFun hu k
  simpa [Pi.single_apply] using this

theorem li_of_adjoint {i : Ω →+* Ω'} (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V')
    (h : ∀ w v, jd w (j v) = i (w v)) {n : ℕ} {b : Fin n → Module.Dual Ω V} (hb : LinearIndependent Ω b) :
    LinearIndependent Ω' fun k => jd (b k) := by
  classical
  refine Fintype.linearIndependent_iff.2 fun c hc l => ?_
  obtain ⟨u, hu⟩ := exists_forms_eq hb l
  have h1 := LinearMap.congr_fun hc (j u)
  simpa [LinearMap.sum_apply, h, hu] using h1

end Lemmas

theorem isVBOn_mono {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T T' : Set (Cpt ξ)} (hT : T' ⊆ T) {r : ℕ} {V : Submodule Ω E}
    (h : L.IsVBOn T r V) : L.IsVBOn T' r V := by
  intro p hp
  obtain ⟨U, hU, b, hb, hfr⟩ := h p (hT hp)
  exact ⟨U, hU, b, hb, fun q hq => hfr q (hT hq)⟩

theorem exists_adjoint {Ω Ω' : Type} [Field Ω] [Field Ω'] {V V' : Type} [AddCommGroup V] [Module Ω V]
    [FiniteDimensional Ω V] [AddCommGroup V'] [Module Ω' V'] {i : Ω →+* Ω'} {j : V →+ V'} (hj : IsExtOver i j)
    (hs : Submodule.span Ω' (Set.range j) = ⊤) :
    Module.finrank Ω' V' = Module.finrank Ω V ∧ ∃ jd : Module.Dual Ω V →+ Module.Dual Ω' V',
      (∀ w v, jd w (j v) = i (w v)) ∧ (∀ (a : Ω) w, jd (a • w) = i a • jd w) ∧
        Submodule.span Ω' (jd '' ((⊤ : Submodule Ω (Module.Dual Ω V)) : Set (Module.Dual Ω V))) = ⊤ := by
  classical
  let v := Module.finBasis Ω V
  have hexp : ∀ u, j u = ∑ k, i (v.repr u k) • j (v k) := fun u => by
    conv_lhs => rw [← v.sum_repr u]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hj.1 _ _
  have hli : LinearIndependent Ω' fun k => j (v k) := by
    have h0 := hj.2 _ v v.linearIndependent
    exact h0
  have hsp : ⊤ ≤ Submodule.span Ω' (Set.range fun k => j (v k)) := by
    rw [← hs]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, rfl⟩
    rw [SetLike.mem_coe, hexp]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let v' := Module.Basis.mk hli hsp
  have hv' : ∀ k, v' k = j (v k) := fun k => by simp [v']
  let jd : Module.Dual Ω V →+ Module.Dual Ω' V' := AddMonoidHom.mk' (fun w => v'.constr Ω' fun k => i (w (v k)))
    (fun a b => by
      rw [← map_add (f := _)]
      congr 1
      funext k
      simp)
  have hjd : ∀ w k, jd w (v' k) = i (w (v k)) := fun w k => by
    show (v'.constr Ω' fun k => i (w (v k))) (v' k) = _
    simp [Module.Basis.constr_basis]
  have hadj : ∀ w u, jd w (j u) = i (w u) := fun w u => by
    rw [hexp u]
    conv_rhs => rw [← v.sum_repr u]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, ← hv', hjd, smul_eq_mul, map_mul]
  refine ⟨?_, jd, hadj, fun a w => v'.ext fun k => ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis v']
    simp
  · rw [hjd]
    show i ((a • w) (v k)) = i a • jd w (v' k)
    rw [hjd]
    simp
  · rw [eq_top_iff]
    rintro w' -
    have hc : ∀ k, jd (v.coord k) = v'.coord k := fun k => v'.ext fun l => by
      rw [hjd]
      simp [Finsupp.single_apply, Module.Basis.coord_apply, eq_comm]
    rw [← v'.sum_dual_apply_smul_coord w']
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨v.coord k, trivial, hc k⟩)

theorem omP_ext : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [CharZero Ω] [Field Ω'] [CharZero Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') (g : A'.X ⟶ A.X) (m : SABMap A'.t A.t g) (j₁ : A.Li →+ A'.Li) (y₀ : Sp Ω ⟶ Xo.XF c) (p : ℕ), p ∈ S → GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ g i → A'.f = g ≫ A.f → A'.R = A.R → IsExtOver i j₁ → (∀ v, (A'.M.pt (j₁ v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) → A.ξ ≫ A.f = y₀ ≫ Y.j → (∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p)) → (HT.omP A p).IsVBOn {q | InFibre A.ξ p q} (Module.finrank Ω A.Li) ⊤ → (HT.omP A' p).IsVBOn {q | InFibre A'.ξ p q} (Module.finrank Ω' A'.Li) ⊤ := by
  intro hW E _ _ _ H D l Xo c Y S Ω Ω' _ _ _ _ i K K' _ _ J J' _ _ y y' A A' g m j₁ y₀ p hp hd hf hR hext hpt hy hζ h
  classical
  have hn : p ^ A.R p ≠ 0 := pow_ne_zero _ (A.S_prime p hp).ne_zero
  obtain ⟨ζ, hζ⟩ := hζ
  have hζi : IsPrimitiveRoot (i ζ) (p ^ A.R p) := hζ.map_of_injective i.injective
  obtain ⟨ζ, rfl⟩ := hζ.isUnit hn
  obtain ⟨ζ₁, hz⟩ := hζi.isUnit hn
  rw [← hz] at hζi
  have hζ' := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hζ₁ := IsPrimitiveRoot.coe_units_iff.1 hζi
  have hy' : A'.ξ ≫ A'.f = (spMap i ≫ y₀) ≫ Y.j := by
    have hd' : A'.ξ ≫ g = spMap i ≫ A.ξ := hd
    rw [hf, ← Category.assoc, hd', Category.assoc, hy, Category.assoc]
  obtain ⟨-, e, -, -, -, -, he, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HF.generic_torsion hW E H D l Xo c Y S Ω K J y A y₀ p ζ hp hy hζ'
  obtain ⟨-, e', -, -, -, -, he', -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HF.generic_torsion hW E H D l Xo c Y S Ω' K' J' y' A' (spMap i ≫ y₀) p ζ₁ hp hy'
    (by rw [hR]; exact hζ₁)
  have := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω A.ξ ℤ _ _ A.tie).2 A.all).1
  have := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω' A'.ξ ℤ _ _ A'.tie).2 A'.all).1
  rw [hR] at he'
  have hfd : FiniteDimensional Ω A.Li :=
    (_root_.GlobalTheory.CompanionTheory.Ar.EigRank.eig_finrank_label E H D l Xo c Y A.X Ω A.ξ A.f y₀ A.t A.m A.Li A.M A.ρ A.cst hy A.cst_over A.act).1
  obtain ⟨-, hspan, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LiePull.main A.X A'.X Ω Ω' A.ξ A'.ξ g i A.t.G A'.t.G m.φ A.Li A'.Li A.M A'.M j₁
    A.tie.gen A'.tie.gen hd m.cart A.t.semi.smooth hpt
  obtain ⟨hrk, jd, hadj, hsm, hjs⟩ := exists_adjoint hext hspan
  have key := (_root_.GlobalTheory.CompanionTheory.Ar.HtPull.main A.X Ω A.ξ A.tie.gen ((_root_.GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal _ Ω A.ξ A.tie.gen A.all).2.2 A.normal) A.t.G A.t.semi
    A.t.PP.L _ (Nat.one_le_iff_ne_zero.2 hn) (A.tors p hp) e he A.Li A.M A'.X Ω' A'.ξ A'.tie.gen
    ((_root_.GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal _ Ω' A'.ξ A'.tie.gen A'.all).2.2 A'.normal) g i hd A'.t.G m.φ m.cart A'.t.PP.L e' he' A'.Li
    A'.M j₁ jd hpt hadj).1
  have h2 := _root_.GlobalTheory.CompanionTheory.Ar.LatPull.isVBOn_pull A.X Ω A.ξ (Module.Dual Ω A.Li) A'.X Ω' A'.ξ g i (Module.Dual Ω' A'.Li) jd (HT.omP A p)
    {q | InFibre A.ξ p q} _ ⊤ hd hsm (fun _ _ hb => li_of_adjoint j₁ jd hadj hb) h
  rw [← key, hjs, ← hrk, ← hR] at h2
  refine isVBOn_mono (fun q hq => ?_) h2
  refine ⟨LatModel.dominates_spec hd q, fun hu => hq ?_⟩
  have hu' : unitAt A.ξ ⟨g q.1, LatModel.dominates_spec hd q⟩ (p : Ω) := hu
  have e1 : (p : Ω') = i (p : Ω) := (map_natCast i p).symm
  have e2 : (p : Ω')⁻¹ = i (p : Ω)⁻¹ := by rw [map_inv₀, map_natCast]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact (map_ne_zero i).2 hu'.1
  · rw [e1]; exact LatModel.dominates_regAt hd q _ hu'.2.1
  · rw [e2]; exact LatModel.dominates_regAt hd q _ hu'.2.2

end GlobalTheory.CompanionTheory.Ar.HFlag
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogForm
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.HInterior

open GlobalTheory.CompanionTheory.Ar.Flat.CptIn.Intr GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

section Noeth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {κ : Type} [Finite κ]

theorem isNoetherianRing_chart (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (hT : CoordTie ℤ ξ x) (c : κ)
    (hc : x c ≠ 0) (U : X.Opens) (hU : IsAffineOpen U)
    (hUm : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (hη : genPt ξ ∈ U) :
    IsNoetherianRing Γ(X, U) := by
  have sp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hUm q).1 hq).1
  let A : Subalgebra ℤ Ω := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  have hreg : ∀ a : Ω, a ∈ A ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
    intro a
    refine (hT.ring c hc a).trans (forall_congr' fun q => imp_congr ?_ Iff.rfl)
    exact ⟨fun hq => (hUm q.1).2 ⟨q.2, hq⟩, fun hq => ((hUm q.1).1 hq).2⟩
  let ρ : Γ(X, U) →+* A := (ev ξ U hη).codRestrict A
    fun s => (hreg _).2 fun q hq => ⟨_, genMap_germ hη q hq s⟩
  have hinj : Function.Injective ρ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro s hs
    have h0 : ev ξ U hη s = 0 := congrArg Subtype.val hs
    refine TopCat.Presheaf.section_ext X.sheaf U s 0 fun q hq => ?_
    apply hT.gen.inj ⟨q, sp q hq⟩
    have h1 := genMap_germ hη ⟨q, sp q hq⟩ hq s
    rw [h0] at h1
    refine h1.trans ?_
    simp only [map_zero]
  have hsurj : Function.Surjective ρ := by
    rintro ⟨a, ha⟩
    obtain ⟨s, hs⟩ := exists_ev_eq hU hη sp a ((hreg a).1 ha)
    exact ⟨s, Subtype.ext hs⟩
  haveI : Algebra.FiniteType ℤ A :=
    (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  exact isNoetherianRing_of_ringEquiv A (RingEquiv.ofBijective ρ ⟨hinj, hsurj⟩).symm

theorem isLocallyNoetherian_of_coordTie (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (hT : CoordTie ℤ ξ x)
    (hall : ∀ q : X, genPt ξ ⤳ q) : IsLocallyNoetherian X := by
  have key : ∀ p : X, ∃ U : X.affineOpens, p ∈ U.1 ∧ IsNoetherianRing Γ(X, U.1) := by
    intro p
    obtain ⟨c, hch⟩ := hT.cover ⟨p, hall p⟩
    obtain ⟨U, hU, hUm⟩ := hT.affine c hch.1
    have hp : p ∈ U := (hUm p).2 ⟨hall p, hch⟩
    exact ⟨⟨U, hU⟩, hp, isNoetherianRing_chart ξ x hT c hch.1 U hU hUm ((hall p).mem_open U.isOpen hp)⟩
  choose S hS hN using key
  exact isLocallyNoetherian_of_affine_cover (S := S)
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hS p⟩) hN

end Noeth

section Form

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem exists_homog_form_point (ξ : Spec (CommRingCat.of Ω) ⟶ X) (y : (Σ k, J k) → Ω)
    (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) (V : X.Opens) (hV : genPt ξ ∈ V) :
    ∃ (f : MRing J) (d : K → ℕ), IsMultiHomog f d ∧ f ∉ mCoordIdeal y ∧ ∀ w ∈ mcPts (mCoordIdeal y), evC w f ≠ 0 →
      ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, CoordsAt ξ y z w ∧ centre z ∈ V := by
  classical
  obtain ⟨c, hch⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
  have hcx := hch.1
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcx k (Finset.mem_univ k)
  obtain ⟨U, hU, hUm⟩ := hT.affine c hcx
  have hη : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, hch⟩
  have sp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hUm q).1 hq).1
  have hreg : ∀ a : Ω, a ∈ chartRingZ y c ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
    intro a
    have h := hT.ring c hcx a
    rw [show (Algebra.adjoin ℤ (Set.range fun j : (∀ k, J k) => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) =
      chartRingZ y c from segre_chart y c hc] at h
    refine h.trans (forall_congr' fun q => imp_congr ?_ Iff.rfl)
    exact ⟨fun hq => (hUm q.1).2 ⟨q.2, hq⟩, fun hq => ((hUm q.1).1 hq).2⟩
  let ρ : Γ(X, U) →+* chartRingZ y c := (ev ξ U hη).codRestrict (chartRingZ y c)
    fun s => (hreg _).2 fun q hq => ⟨_, genMap_germ hη q hq s⟩
  obtain ⟨s, hsV, hsη⟩ := hU.exists_basicOpen_le (V := V) ⟨genPt ξ, hV⟩ hη
  have ha0 : ev ξ U hη s ≠ 0 :=
    (((Scheme.mem_basicOpen X s _ hη).1 hsη).map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  obtain ⟨g₀, hg₀⟩ := ratMap_surjective y c (ρ s)
  obtain ⟨m, G₀, hG₀, eG⟩ := exists_form c g₀
  have hy₀ : aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g₀ = ev ξ U hη s := by
    rw [← ratMap_coe, hg₀]
    rfl
  have hf0 : aeval y (G₀ * cMon c 1) ≠ 0 := by
    rw [map_mul, aeval_cMon, ← eG Ω y hc, hy₀]
    exact mul_ne_zero (mul_ne_zero ha0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)))
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  refine ⟨G₀ * cMon c 1, m + 1, homog_mul hG₀ (homog_cMon c 1), fun hmem => hf0 ?_, fun w hw hne => ?_⟩
  · have h := aeval_scaled y (fun _ => 1) (G₀ * cMon c 1)
    have h0 : mConeMap y (G₀ * cMon c 1) = 0 := hmem
    rw [h0, map_zero] at h
    simpa only [mul_one] using h
  have hne' : aeval w (G₀ * cMon c 1) ≠ 0 := by
    rw [← evC_eq_aeval]
    exact hne
  rw [map_mul, aeval_cMon] at hne'
  have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by
    have := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hne') k (Finset.mem_univ k)
    simpa using this
  obtain ⟨e, he⟩ := exists_chartEval y c hc w hw hwc
  obtain ⟨z, hz, hval⟩ := exists_pt hU (e.comp ρ)
  have hval' : ∀ k i, ∃ s : Γ(X, U), ev ξ U hη s = y ⟨k, i⟩ / y ⟨k, c k⟩ ∧
      (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz s) = w ⟨k, i⟩ / w ⟨k, c k⟩ := by
    intro k i
    have hm : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c := Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩
    obtain ⟨s, hs⟩ := exists_ev_eq hU hη sp _ ((hreg _).1 hm)
    refine ⟨s, hs, ?_⟩
    have e1 : ρ s = ratMap y c (MvPolynomial.X ⟨k, i⟩) := Subtype.ext (by rw [ratMap_coe, aeval_X]; exact hs)
    rw [hval]
    change e (ρ s) = _
    rw [e1, he, aeval_X]
  have hs0 : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz s) ≠ 0 := by
    rw [hval]
    change e (ρ s) ≠ 0
    rw [← hg₀, he]
    intro h0
    apply left_ne_zero_of_mul hne'
    rw [← eG ℂ w hwc, h0, zero_mul]
  refine ⟨z, ⟨fun k => ⟨c k, (IsUnit.mk0 _ (hwc k))⟩, fun k c₀ hu => ?_⟩, hsV ?_⟩
  · have hw0 : w ⟨k, c₀⟩ ≠ 0 := hu.ne_zero
    obtain ⟨sv, hsv, hev⟩ := hval' k c₀
    have hev0 : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz sv) ≠ 0 := by
      rw [hev]
      exact div_ne_zero hw0 (hwc k)
    have hy0 : y ⟨k, c₀⟩ ≠ 0 := by
      intro h0
      apply hev0
      have h1 : ρ sv = 0 := Subtype.ext (by
        change ev ξ U hη sv = 0
        rw [hsv, h0, zero_div])
      rw [hval]
      change e (ρ sv) = 0
      rw [h1, map_zero]
    refine ⟨hy0, fun i => ?_⟩
    obtain ⟨su, hsu, heu⟩ := hval' k i
    refine ⟨w ⟨k, i⟩ / w ⟨k, c₀⟩, ?_, by field_simp⟩
    have h := valAt_quot hη sp z hz su sv hev0
    rw [hsu, hsv, heu, hev, div_div_div_cancel_right₀ (hc k), div_div_div_cancel_right₀ (hwc k)] at h
    exact h
  · exact (Scheme.mem_basicOpen X s _ hz).2
      (isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ (IsUnit.mk0 _ hs0))

end Form

end GlobalTheory.CompanionTheory.Ar.Cmp.HInterior

theorem GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c), A.ξ ≫ A.f = x ≫ Y.j → Mono (spMap β) → ∃ (b : MRing ι) (d : K → ℕ), IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ ∀ w ∈ mcPts (mCoordIdeal y), evC w b ≠ 0 → ∃ z : Spec (CommRingCat.of ℂ) ⟶ A.X, CoordsAt A.ξ y z w ∧ A.Interior z := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ ι _ y A x hx _
  haveI : IsLocallyNoetherian A.X := GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.isLocallyNoetherian_of_coordTie A.ξ _ A.tie A.all
  let V : A.X.Opens := ⟨abLocus A.t.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian A.t.G A.t.semi⟩
  have hV : genPt A.ξ ∈ V := by
    refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 (genPt A.ξ)).1 ?_
    have h1 : A.f (genPt A.ξ) = Y.j (x (IsLocalRing.closedPoint Ω)) := by
      have := congrArg (fun g : Sp Ω ⟶ Y.X => g (IsLocalRing.closedPoint Ω)) hx
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans (this.trans (Scheme.Hom.comp_apply _ _ _))
    rw [h1]
    exact GlobalTheory.ModelScope.range_j_subset_abLocus Y ⟨_, rfl⟩
  obtain ⟨b, d, hb, hbI, hw⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_homog_form_point A.ξ y A.tie V hV
  refine ⟨b, d, hb, hbI, fun w hwm hne => ?_⟩
  obtain ⟨z, hz, hzV⟩ := hw w hwm hne
  exact ⟨z, hz, hzV⟩
end
end

