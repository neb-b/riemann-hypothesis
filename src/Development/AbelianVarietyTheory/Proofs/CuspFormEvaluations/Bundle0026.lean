module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsValueAtJetPointCmFrameSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameSymmetryTrivial
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal.Sym

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

theorem tay_coord {g : ℕ} (k : Fin g) :
    tay (fun v : Fin g → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  classical
  have hθ : ContDiffAt ℂ ω (fun v : Fin g → ℂ => v k) 0 := (contDiff_apply ℂ (fun _ => ℂ) k).contDiffAt
  have eq_of_cc (F G : MvPowerSeries (Fin 1 × Fin g) ℂ)
      (h : ∀ l : List (Fin 1 × Fin g), MvPowerSeries.constantCoeff (l.foldr (fun q H => MvPowerSeries.pderiv q H) F) =
        MvPowerSeries.constantCoeff (l.foldr (fun q H => MvPowerSeries.pderiv q H) G)) : F = G := by
    have coeff_foldr (l : List (Fin 1 × Fin g)) (m : (Fin 1 × Fin g) →₀ ℕ) :
        ∃ c : ℂ, c ≠ 0 ∧ ∀ F : MvPowerSeries (Fin 1 × Fin g) ℂ,
          MvPowerSeries.coeff m (l.foldr (fun q G => MvPowerSeries.pderiv q G) F) =
            c * MvPowerSeries.coeff (m + (l.map fun q => Finsupp.single q 1).sum) F := by
      induction l generalizing m with
      | nil => exact ⟨1, one_ne_zero, fun F => by simp⟩
      | cons q l ih =>
        obtain ⟨c, hc, hF⟩ := ih (m + Finsupp.single q 1)
        refine ⟨c * ((m q : ℂ) + 1), mul_ne_zero hc (Nat.cast_add_one_ne_zero _), fun F => ?_⟩
        simp only [List.foldr_cons]
        rw [MvPowerSeries.coeff_pderiv, hF, List.map_cons, List.sum_cons, add_assoc]
        ring
    have sum_single_toList (m : (Fin 1 × Fin g) →₀ ℕ) :
        ((Finsupp.toMultiset m).toList.map fun q => Finsupp.single q 1).sum = m := by
      have hs : ∀ t : Multiset (Fin 1 × Fin g), (t.map fun q => Finsupp.single q 1).sum = Multiset.toFinsupp t := by
        intro t
        induction t using Multiset.induction_on with
        | empty => simp
        | cons a t ih =>
          rw [Multiset.map_cons, Multiset.sum_cons, ih, ← Multiset.singleton_add, Multiset.toFinsupp_add,
            Multiset.toFinsupp_singleton]
      have h2 := hs (Finsupp.toMultiset m)
      rw [Finsupp.toMultiset_toFinsupp] at h2
      calc
        _ = (Multiset.map (fun q => Finsupp.single q 1) (Finsupp.toMultiset m)).sum := by
          rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList]
        _ = m := h2
    ext m
    have h1 := h (Finsupp.toMultiset m).toList
    obtain ⟨c, hc, h0⟩ := coeff_foldr (Finsupp.toMultiset m).toList 0
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      h0, h0, zero_add, sum_single_toList] at h1
    exact mul_left_cancel₀ hc h1
  refine eq_of_cc _ _ fun l => ?_
  rcases l.eq_nil_or_concat with rfl | ⟨l', ⟨a, j⟩, rfl⟩
  · simp only [List.foldr_nil, constantCoeff_tay, TM.mD_zero, MvPowerSeries.constantCoeff_X, Pi.zero_apply]
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    have hd : (fun y : Fin g → ℂ => fderiv ℂ (fun v : Fin g → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j (1 : ℂ) : Fin g → ℂ) k := by
      funext y
      exact congrArg (fun T : (Fin g → ℂ) →L[ℂ] ℂ => T (Pi.single j 1))
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) k).fderiv
    rw [List.concat_eq_append, List.foldr_append, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [TM.pderiv_tay hθ, hd, TM.tay_const, MvPowerSeries.pderiv_X]
    congr 2
    by_cases h : k = j
    · subst h; simp
    · simp [h, Ne.symm h, Pi.single_apply]


theorem psJet_X {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (s : κ) :
    psJet m (MvPowerSeries.X s : MvPowerSeries κ ℂ) = Ideal.Quotient.mk _ (MvPolynomial.X s) := by
  rw [← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem jetN_coord {n g : ℕ} (m : ℕ) (i : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => w i j) = Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
  unfold jetN jetOf
  show renN n g m (psJet m (tay (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j))) 0)) = _
  rw [tay_coord, psJet_X]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
  rw [MvPolynomial.aeval_X, Equiv.symm_apply_apply]

def swapL (g : ℕ) : (Fin 2 → Fin g → ℂ) →ₗ[ℂ] (Fin 2 → Fin g → ℂ) :=
  LinearMap.pi fun i => LinearMap.proj (Equiv.swap (0 : Fin 2) 1 i)

def swapI : ULift.{0} (Finset (Fin 2)) ≃ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.finsetCongr (Equiv.swap (0 : Fin 2) 1)).trans Equiv.ulift.symm)

theorem psumL_swap (g : ℕ) (I : ULift.{0} (Finset (Fin 2))) :
    psumL 2 g I ∘ₗ swapL g = psumL 2 g (swapI I) := by
  refine LinearMap.ext fun w => ?_
  simp [psumL, swapL, swapI, Equiv.finsetCongr_apply]

theorem cε_swap (I : ULift.{0} (Finset (Fin 2))) : cε 2 (swapI I) = cε 2 I := by
  simp [cε, swapI, Equiv.finsetCongr_apply]

theorem jetMap_unique {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n m : ℕ} {ψ ψ' : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) (h' : Φ.JetMap m ψ' Λ) : ψ = ψ' := by
  obtain ⟨_, rfl⟩ := h
  obtain ⟨_, rfl⟩ := h'
  rfl

theorem sy_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 2 × Fin g) m)ˣ, (u : Jet ℂ (Fin 2 × Fin g) m) = psJet m (anFB ty).sy ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m) (scaleGen _ _ (unitΓ u⁻¹) (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hI e he m
  refine ⟨1, ?_, ?_⟩
  · show (1 : Jet ℂ (Fin 2 × Fin g) m) = psJet m 1
    rw [← MvPolynomial.coe_one, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, map_one]
  have hR := (he m).2
  have hS := _root_.GlobalTheory.JetLinSub.jetRd_linSubst _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr 2 2 m (swapL g)
    (fun p : Fin 2 × Fin g => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] :
      Fin 2 → Fin g → MvPolynomial (Fin 2 × Fin g) ℂ) p.1 p.2) (by
      rintro ⟨i, j⟩
      rw [psJet_X]
      refine Eq.trans ?_ (jetN_coord m (Equiv.swap (0 : Fin 2) 1 i) j).symm
      show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
      fin_cases i <;> simp) _ _ _ _ _ hR
  have hC := _root_.GlobalTheory.AnVal.JetCorr.corr_of_jetRd _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr hI 2 m _ _ _ _ _ _ _ _ _ _ hR hS (by
    intro ψ
    refine (Fintype.sum_equiv swapI _ _ fun I => ?_).symm
    have h1 := hS.1 I
    beta_reduce at h1 ⊢
    rw [psumL_swap] at h1
    rw [jetMap_unique _ h1 (hR.1 (swapI I)), cε_swap])
  intro j j' h1 h2 h3
  refine (hC j j' h1 h2 h3).trans ?_
  congr 1
  show _ = res le_top (unitΓ (1 : (Jet ℂ (Fin 2 × Fin g) m)ˣ)⁻¹) * _
  rw [inv_one, unitΓ, map_one]
  have : ∀ (X : Scheme.{0}) (U : X.Opens), res (le_top : U ≤ ⊤) (1 : Γ(X, ⊤)ˣ) = 1 := fun X U => map_one _
  rw [this]
  exact (_root_.one_mul _).symm

end GlobalTheory.AnVal.Sym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardNonisometricCmTorusDataLe
section
open NumberField

namespace GlobalTheory.DataClassCount

open scoped nonZeroDivisors
open Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HermModel

variable {E : Type} [Field E] [NumberField E]

theorem mem_of_forall_mul_smul {V : Type} [AddCommGroup V] [Module E V]
    (AA : Submodule (𝓞 E) E) (hfg : AA.FG) (h0 : AA ≠ ⊥) (N : AddSubmonoid V) (v : V)
    (h : ∀ a ∈ AA, ∀ b : E, (∀ c ∈ AA, ∃ o : 𝓞 E, (o : E) = b * c) → (a * b) • v ∈ N) :
    v ∈ N := by
  let I : FractionalIdeal (𝓞 E)⁰ E := ⟨AA, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI : I ≠ 0 := fun h => h0 ((congrArg FractionalIdeal.coeToSubmodule h).trans
    FractionalIdeal.coe_zero)
  have h1 : (1 : E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hI]
    exact FractionalIdeal.one_mem_one _
  have key : ∀ r ∈ I * I⁻¹, r • v ∈ N := by
    intro r hr
    refine FractionalIdeal.mul_induction_on (C := fun r => r • v ∈ N) hr ?_ ?_
    · intro a ha b hb
      refine h a ha b fun c hc => ?_
      exact (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hI).1 hb c hc)
    · intro x y hx hy
      rw [add_smul]
      exact N.add_mem hx hy
  simpa using key 1 h1

def divLat {r : ℕ} (AA : Submodule (𝓞 E) E) (M : Submodule (𝓞 E) (Fin r → E)) :
    Submodule (𝓞 E) (Fin r → E) where
  carrier := {v | ∀ a ∈ AA, a • v ∈ M}
  add_mem' := fun hx hy a ha => by
    rw [smul_add]; exact M.add_mem (hx a ha) (hy a ha)
  zero_mem' := fun a _ => by rw [smul_zero]; exact M.zero_mem
  smul_mem' := fun c x hx a ha => by
    rw [smul_comm]; exact M.smul_mem c (hx a ha)

theorem smul_mem_divLat {r : ℕ} {AA : Submodule (𝓞 E) E} {M : Submodule (𝓞 E) (Fin r → E)}
    {v : Fin r → E} (hv : v ∈ M) {b : E} (hb : ∀ c ∈ AA, ∃ o : 𝓞 E, (o : E) = b * c) :
    b • v ∈ divLat AA M := by
  intro a ha
  obtain ⟨o, ho⟩ := hb a ha
  rw [smul_smul, mul_comm, ← ho]
  exact M.smul_mem o hv

theorem mem_iff_divLat {r : ℕ} {AA : Submodule (𝓞 E) E} (hfg : AA.FG) (h0 : AA ≠ ⊥)
    (M : Submodule (𝓞 E) (Fin r → E)) (v : Fin r → E) :
    v ∈ M ↔ ∀ b : E, (∀ c ∈ AA, ∃ o : 𝓞 E, (o : E) = b * c) → b • v ∈ divLat AA M := by
  refine ⟨fun hv b hb => smul_mem_divLat hv hb, fun h => ?_⟩
  refine mem_of_forall_mul_smul AA hfg h0 M.toAddSubmonoid v fun a ha b hb => ?_
  rw [mul_smul]
  exact h b hb a ha

theorem isLattice_divLat {r : ℕ} {AA : Submodule (𝓞 E) E} (hfg : AA.FG) (h0 : AA ≠ ⊥)
    {M : Submodule (𝓞 E) (Fin r → E)} (hM : M.FG)
    (hs : Submodule.span E (M : Set (Fin r → E)) = ⊤) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (divLat AA M) := by
  constructor
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    let f : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (LinearMap.lsmul E (Fin r → E) a).restrictScalars _
    have hf : Function.Injective f := smul_right_injective _ ha0
    apply Submodule.fg_of_fg_map_injective f hf
    haveI : IsNoetherian (𝓞 E) M := isNoetherian_of_fg_of_noetherian M hM
    refine Submodule.FG.of_le_of_isNoetherian (T := M) ?_
    rintro _ ⟨v, hv, rfl⟩
    exact hv a ha
  · apply top_unique
    rw [← hs]
    rw [Submodule.span_le]
    intro v hv
    apply mem_of_forall_mul_smul AA hfg h0 (Submodule.span E (divLat AA M : Set (Fin r → E))).toAddSubmonoid v
    intro a ha b hb
    rw [mul_smul]
    exact Submodule.smul_mem _ a (Submodule.subset_span (smul_mem_divLat hv hb))
variable [IsCMField E]

theorem herm_smul_smul {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ξ a b : E) (x y : Fin r → E) :
    ξ * FD.herm G (a • x) (b • y) = ξ * FD.herm G x y * a * FD.cc b := by
  rw [herm_smul_left, herm_smul_right]; ring

theorem selfDual_divLat {r : ℕ} {AA : Submodule (𝓞 E) E} (hfg : AA.FG) (h0 : AA ≠ ⊥) (ξ : E)
    (hA : ∀ x : E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ E (ξ * x * a * FD.cc b) = z) ↔
      IsIntegral ℤ x) (G : Matrix (Fin r) (Fin r) E) {M : Submodule (𝓞 E) (Fin r → E)}
    (hM : ∀ v, (∀ y ∈ M, ∃ n : ℤ, Algebra.trace ℚ E (ξ * FD.herm G v y) = n) ↔ v ∈ M) :
    (∀ x ∈ divLat AA M, ∀ y ∈ divLat AA M, IsIntegral ℤ (FD.herm G x y)) ∧
      ∀ x, (∀ y ∈ divLat AA M, IsIntegral ℤ (FD.herm G x y)) → x ∈ divLat AA M := by
  constructor
  · intro x hx y hy
    refine (hA _).1 fun a ha b hb => ?_
    rw [← herm_smul_smul]
    exact (hM _).2 (hx a ha) _ (hy b hb)
  · intro x hx a ha
    refine (hM _).1 fun y hy => ?_
    let N : AddSubmonoid (Fin r → E) :=
      { carrier := {y | ∃ n : ℤ, Algebra.trace ℚ E (ξ * FD.herm G (a • x) y) = n}
        add_mem' := by
          rintro u w ⟨n, hn⟩ ⟨k, hk⟩
          refine ⟨n + k, ?_⟩
          rw [herm_add_right, mul_add, map_add (f := _), hn, hk]
          push_cast; rfl
        zero_mem' := ⟨0, by rw [herm_zero_right]; simp⟩ }
    refine mem_of_forall_mul_smul AA hfg h0 N y fun a' ha' b hb => ?_
    change ∃ n : ℤ, _
    rw [mul_smul, herm_smul_smul]
    exact (hA _).2 (hx _ (smul_mem_divLat hy hb)) a ha a' ha'

theorem exists_isometry {H : Host E} (D D' : Datum H) {r : ℕ} (ξ : E)
    (G : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))
    (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (hφ : Function.Injective φ) (hφ' : Function.Injective φ')
    (hE : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm G (φ x) (φ y)))
    (hE' : ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm G (φ' x) (φ' y)))
    (g : (Fin r → E) ≃ₗ[E] (Fin r → E)) (hg : ∀ x y, FD.herm G (g x) (g y) = FD.herm G x y)
    (hm : ∀ x, x ∈ LinearMap.range φ ↔ g x ∈ LinearMap.range φ') :
    ∃ gam : D.La ≃ₗ[𝓞 E] D'.La, ∀ a b, D'.EF (gam a) (gam b) = D.EF a b := by
  have hmap : (LinearMap.range φ).map
      ((g.restrictScalars (𝓞 E) : (Fin r → E) ≃ₗ[𝓞 E] (Fin r → E)) :
        (Fin r → E) →ₗ[𝓞 E] (Fin r → E)) = LinearMap.range φ' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hm x).1 hx
    · intro hy
      refine ⟨g.symm y, (hm _).2 (by rwa [g.apply_symm_apply]), g.apply_symm_apply y⟩
  let gam : D.La ≃ₗ[𝓞 E] D'.La := ((LinearEquiv.ofInjective φ hφ).trans
    (LinearEquiv.ofSubmodules (g.restrictScalars (𝓞 E)) _ _ hmap)).trans
      (LinearEquiv.ofInjective φ' hφ').symm
  have hgam : ∀ a, φ' (gam a) = g (φ a) := fun a =>
    congrArg Subtype.val ((LinearEquiv.ofInjective φ' hφ').apply_symm_apply _)
  refine ⟨gam, fun a b => ?_⟩
  have : ((D'.EF (gam a) (gam b) : ℤ) : ℚ) = D.EF a b := by
    rw [hE', hE, hgam, hgam, hg]
  exact_mod_cast this

end GlobalTheory.DataClassCount

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory


open DataClassCount in
theorem card_nonisometric_data_le : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q r : ℕ), r = p + q → ∀ (ξ : E) (AA : Submodule (𝓞 E) E), FD.cc ξ = -ξ → ξ ≠ 0 → AA.FG → AA ≠ ⊥ → (∀ x : E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ E (ξ * x * a * FD.cc b) = z) ↔ IsIntegral ℤ x) → ∀ (m : ℕ) (Di : Fin m → Datum H), (∀ i, (Di i).p = p ∧ (Di i).q = q) → (∀ i j (gam : (Di i).La ≃ₗ[𝓞 E] (Di j).La), (∀ a b, (Di j).EF (gam a) (gam b) = (Di i).EF a b) → i = j) → (m : ℝ) ≤ (1 + 2 * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2) * (r * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2) := by
  intro hH E _ _ _ H p q r hr ξ AA hξ hξ0 hfg h0 hA m Di hpq hne
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.cast_zero]
    positivity
  let i0 : Fin m := ⟨0, hm⟩
  obtain ⟨G, φ0, hM0⟩ := GlobalTheory.exists_herm_coord_of_datum E H (Di i0) ξ hξ hξ0 r
    (by rw [(hpq i0).1, (hpq i0).2, hr])
  have hex := fun i => GlobalTheory.model_in_same_space (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt hH) hH E H
    (Di i0) (Di i) r ξ G φ0 (by rw [(hpq i0).1, (hpq i).1]) (by rw [(hpq i0).2, (hpq i).2]) hξ hM0
  choose φ hφ using hex
  obtain ⟨S, -, hS, hcard, -⟩ := GlobalTheory.exists_finset_selfDual_classes_herm G hM0.2.2.1
  have hcl := fun i => by
    have h := GlobalTheory.HermModel.rank_integral_selfDual E H (Di i) r ξ G (φ i) hξ (hφ i)
    have hsd := selfDual_divLat hfg h0 ξ hA G (M := LinearMap.range (φ i)) fun v => by
      rw [← h.2.2.2 v]
      exact ⟨fun h y => h _ ⟨y, rfl⟩, by rintro h _ ⟨y, rfl⟩; exact h y⟩
    exact hS _ (isLattice_divLat hfg h0 h.2.1 (hφ i).2.1) hsd.1 hsd.2
  choose L hL γ hγ hmem using hcl
  refine le_trans ?_ hcard
  have hinj : Function.Injective L := by
    intro i j hij
    let g : ∀ k : Fin m, (Fin r → E) ≃ₗ[E] (Fin r → E) := fun k =>
      Matrix.toLin'OfInv (γ k).inv_mul (γ k).mul_inv
    have hg : ∀ k x y, FD.herm G (g k x) (g k y) = FD.herm G x y := hγ
    have hgm : ∀ k x, x ∈ L k ↔ g k x ∈ divLat AA (LinearMap.range (φ k)) := hmem
    obtain ⟨gam, hgam⟩ := exists_isometry (Di i) (Di j) ξ G (φ i) (φ j) (hφ i).1 (hφ j).1
      (hφ i).2.2.2.2 (hφ j).2.2.2.2 ((g i).symm.trans (g j))
      (fun x y => by
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hg, ← hg i,
          LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
      (fun x => by
        rw [mem_iff_divLat hfg h0, mem_iff_divLat hfg h0]
        refine forall₂_congr fun b _ => ?_
        rw [← map_smul, LinearEquiv.trans_apply, ← hgm, ← hij, hgm, LinearEquiv.apply_symm_apply])
    exact hne i j gam hgam
  have := Finset.card_le_card_of_injOn (s := Finset.univ) (t := S) L (fun i _ => hL i) hinj.injOn
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJetsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (n m : ℕ), (∀ i : Fin n, Φ.toAnFr.JetMap m (jpt y g Φ.jx m i).left (LinearMap.proj i)) ∧ Φ.toAnFr.JetMap m (1 : jO y g m n ⟶ Xo.univ.t.G).left 0 ∧ (∀ (a b : jO y g m n ⟶ Xo.univ.t.G) (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m b.left Λ' → Φ.toAnFr.JetMap m (a * b).left (Λ + Λ') ∧ ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left), (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hq m) ∧ (∀ (a : jO y g m n ⟶ Xo.univ.t.G) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (α : 𝓞 E), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m (a ≫ Xo.univ.t.act.act α).left (tyAct ty α ∘ₗ Λ)) ∧ Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) := by
  first | exact @GlobalTheory.AnVal.jetPts_jetMap | exact GlobalTheory.AnVal.jetPts_jetMap | (intros; apply GlobalTheory.AnVal.jetPts_jetMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsValueAtJetPointCmFrameSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isValueAt_jetPoint_cmFrame_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (m k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.Rd k F θ → Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → ∃ F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y g m 1)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y g m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧ IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (Φ.jx m) τ (toΓ _ (jetOf m θ)) := by
  first | exact @GlobalTheory.JetVal.isValueAt_jetPt | exact GlobalTheory.JetVal.isValueAt_jetPt | (intros; apply GlobalTheory.JetVal.isValueAt_jetPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingOfThetaGroupAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem exists_wchart_complexPt {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Z ⟶ X)) (q : Sp ℂ ⟶ Z) : ∃ j : K → L.ι, ⊤ ≤ q ⁻¹ᵁ LB.wchart L φ j := by
  obtain ⟨hcov, -, -⟩ := hL
  have hmem : ∀ y : X, ∃ i, y ∈ L.U i := by
    intro y
    have hy : y ∈ (⨆ i, L.U i) := by rw [hcov]; trivial
    exact (TopologicalSpace.Opens.mem_iSup).1 hy
  have hsub : Subsingleton (Sp ℂ) := by
    change Subsingleton (PrimeSpectrum ℂ)
    infer_instance
  have p0 : Sp ℂ := by
    change PrimeSpectrum ℂ
    exact default
  choose j hj using fun k => hmem (φ k (q p0))
  refine ⟨j, fun y _ => ?_⟩
  rw [Subsingleton.elim y p0]
  show q p0 ∈ L.wchart φ j
  unfold LB.wchart
  exact Set.mem_iInter.2 fun k => hj k

theorem AnFr.rd_of_isActOf : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Φ.ThConst k U x c → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fun z => c * fock Φ.Hm k x θ z) := by
  intro S A _ _ L x0 g Φ k U x c s s' θ hc ha hr
  obtain ⟨-, hz⟩ := hc
  have hfst : translT A U.pt ≫ fst (Over.mk x0) A = fst (Over.mk x0) A := by
    unfold translT
    exact lift_fst _ _
  have hsnd : translT A U.pt ≫ snd (Over.mk x0) A = translPt A U.pt := by
    unfold translT
    exact lift_snd _ _
  have htw : IsTwistPull A L.L (translT A U.pt) (translPt A U.pt) hsnd k k U.φ s s' := by
    unfold IsActOf at ha
    exact ha
  have hcond : ∀ z, (ptSecT A (Φ.e z)).left ≫ (translPt A U.pt).left = (Φ.e (x + z)).left ∧
      ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ
          LB.wchart L.L ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] j ∧
        valAt' (ptSecT A (Φ.e z)).left
            (LB.wchart L.L ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] j) (U.φ.s j).val =
          c * fock Φ.Hm k x (fun _ => 1) z * (Φ.fr (j 0) z ^ k * Φ.fr (j 1) (x + z) ^ (-k)) := by
    intro z
    obtain ⟨hmaps, hval⟩ := hz z
    refine ⟨by simpa using hmaps 1, ?_⟩
    obtain ⟨j, hj⟩ := exists_wchart_complexPt L.L L.isLB
      ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] (ptSecT A (Φ.e z)).left
    refine ⟨j, hj, ?_⟩
    rw [hval j hj, Fin.prod_univ_two]
    simp
  have key := GlobalTheory.T.reading_twisted_pullback S A L x0 g Φ (translT A U.pt) (translPt A U.pt) hsnd k k U.φ s s' θ
    (fun z => x + z) (fun z => c * fock Φ.Hm k x (fun _ => 1) z) hfst htw hr hcond
  have hfun : (fun z => c * fock Φ.Hm k x (fun _ => 1) z * θ (x + z)) = fun z => c * fock Φ.Hm k x θ z := by
    funext z
    simp only [fock]
    rw [add_comm x z]
    ring
  rw [← hfun]
  exact key

end GlobalTheory.AnVal
end

