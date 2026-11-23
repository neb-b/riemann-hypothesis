module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetRdMulInvPow
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff

namespace GlobalTheory.AnVal.JetAlg

def AnO {n g : ℕ} (f : (Fin n → Fin g → ℂ) → ℂ) : Prop := ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0

private lemma jetN_eq_renN_psJet_tay {n g : ℕ} (m : ℕ) (f : (Fin n → Fin g → ℂ) → ℂ) :
    jetN m f = renN n g m (psJet m (tay (fun v => f (colsOf n g v)) 0)) := by
  rfl

theorem jetN_mul {n g : ℕ} (m : ℕ) {f h : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (hh : AnO h) :
    jetN m (fun w => f w * h w) = jetN m f * jetN m h := by
  rw [jetN_eq_renN_psJet_tay, jetN_eq_renN_psJet_tay, jetN_eq_renN_psJet_tay, ← map_mul, ← FBIdJet.psJet_mul]
  congr 2
  exact (TM.taylor_multiplication.1 _ _ _ hf hh).1

theorem jetN_one {n g : ℕ} (m : ℕ) : jetN m (fun _ : Fin n → Fin g → ℂ => (1 : ℂ)) = 1 := by
  have hc := TM.taylor_multiplication.2.1 (n * g) 1
  simp only [jetN, jetOf]
  rw [hc, map_one, FBIdJet.psJet_one, map_one]

theorem jetN_pow {n g : ℕ} (m : ℕ) {f : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (p : ℕ) :
    jetN m (fun w => f w ^ p) = jetN m f ^ p := by
  induction p with
  | zero =>
    simp only [pow_zero]
    exact jetN_one m
  | succ p ih =>
    have hp : AnO fun w => f w ^ p := by
      unfold AnO at hf ⊢
      exact hf.pow p
    rw [show (fun w => f w ^ (p + 1)) = fun w => f w ^ p * f w from funext fun w => pow_succ (f w) p,
      jetN_mul m hp hf, ih]
    exact (pow_succ _ _).symm

theorem jetN_inv_mul {n g : ℕ} (m : ℕ) {f : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (h0 : f (colsOf n g 0) ≠ 0) :
    jetN m (fun w => (f w)⁻¹) * jetN m f = 1 := by
  have hf' : ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0 := hf
  have hinv : AnO fun w => (f w)⁻¹ := hf'.inv h0
  rw [← jetN_mul m hinv hf]
  have hev : (fun v => (f (colsOf n g v))⁻¹ * f (colsOf n g v)) =ᶠ[nhds 0] fun _ => (1 : ℂ) := by
    filter_upwards [hf'.continuousAt.eventually_ne h0] with v hv
    exact inv_mul_cancel₀ hv
  have h1 := jetN_one (n := n) (g := g) m
  simp only [jetN, jetOf] at h1 ⊢
  rw [TM.taylor_multiplication.2.2 _ _ _ hev]
  exact h1

theorem AnO.zpow {n g : ℕ} {f : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (h0 : f (colsOf n g 0) ≠ 0) (k : ℤ) :
    AnO fun w => f w ^ k := by
  have hf' : ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0 := hf
  show ContDiffAt ℂ ω (fun v => f (colsOf n g v) ^ k) 0
  obtain ⟨p, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp only [zpow_natCast]
    exact hf'.pow p
  · simp only [zpow_neg, zpow_natCast]
    exact (hf'.pow p).inv (pow_ne_zero _ h0)

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {n m : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem origin_mem {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left} {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hψ : Φ.JetMap m ψ Λ) {U : A.left.Opens} (hU : ⊤ ≤ ψ ⁻¹ᵁ U) :
    ⊤ ≤ (Φ.e (Λ (colsOf n g 0))).left ⁻¹ᵁ U := by
  obtain ⟨hol, rfl⟩ := hψ
  have hz : IsLocalHom (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) := by
    unfold jetZero
    exact isLocalHom_jetMap _ _
  have hr : IsLocalHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) := by
    unfold renN
    exact isLocalHom_jetMap _ _
  have hc : ∀ F : (Fin (n * g) → ℂ) → ℂ, jetAug (jetOf m F) = F 0 := by
    intro F
    unfold jetOf psJet
    rw [jetAug_mk, FBIdJet.psTrunc_eq]
    show AddMonoidAlgebra.coeff _ 0 = _
    rw [MvPowerSeries.coeff_truncTotal _ (by simp), coeff_tay]
    simp [dirs, fct, TM.mD_zero]
  have hk : ∀ c : ℂ, jetOf m (fun _ : Fin (n * g) → ℂ => c) = algebraMap ℂ _ c := by
    intro c
    unfold jetOf psJet
    rw [TM.taylor_multiplication.2.1, ← MvPolynomial.coe_C, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]
    rfl
  have key := jetPt_precomp _ (fun _ => (Φ.e (Λ (colsOf n g 0))).left) hol (isHolFam_const _) rfl m
    (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) (fun U _ f => by
      rw [AlgHom.coe_toRingHom, jetZero_eq, hc, hk])
  rw [← jetPt_const] at key
  intro p _
  have h1 := hU (show IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m) ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
  have h2 := congrArg (fun φ => φ (IsLocalRing.closedPoint (Jet ℂ (Fin 1 × Fin (n * g)) m))) key
  unfold spMap at h1 h2
  simp only [Scheme.Hom.comp_apply] at h1 h2
  have hz' : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom
      (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m))) := hz
  have hr' : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom
      (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m))) := hr
  have q1 : (Spec.map (CommRingCat.ofHom (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m)))
      (IsLocalRing.closedPoint (Jet ℂ (Fin 1 × Fin (n * g)) m)) = IsLocalRing.closedPoint _ :=
    AlgebraicGeometry.Spec_closedPoint
  have q2 : (Spec.map (CommRingCat.ofHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m)))
      (IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m)) = IsLocalRing.closedPoint _ :=
    AlgebraicGeometry.Spec_closedPoint
  have hp : ∀ q r : PrimeSpectrum ℂ, q = r := fun q r =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)
  show (Over.Hom.left (Φ.e (Λ (colsOf n g 0)))) p ∈ U
  rw [hp p ((Spec.map (CommRingCat.ofHom (algebraMap ℂ (Jet ℂ (Fin 1 × Fin (n * g)) m))))
    (IsLocalRing.closedPoint (Jet ℂ (Fin 1 × Fin (n * g)) m)))]
  refine (congrArg (fun z => z ∈ U) h2).mp ?_
  exact (congrArg (fun z => (jetPt (fun v => Over.Hom.left (Φ.e (Λ (colsOf n g v)))) hol m) z ∈ U)
    (q1.trans q2.symm)).mpr h1

theorem anO_fr {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left} {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hψ : Φ.JetMap m ψ Λ) {j : L.L.ι} (hU : ⊤ ≤ ψ ⁻¹ᵁ L.L.U j) : AnO fun w => Φ.fr j (Λ w) := by
  have h0 := origin_mem Φ hψ hU
  have hopen := (Φ.hol (L.L.U j) 0).1
  have han : AnalyticAt ℂ (Φ.fr j) (Λ (colsOf n g 0)) :=
    ReciprocityTheory.AnForm.Osgood.osgood g _ _ hopen (Φ.fr_hol j) _ h0
  have hc : ContDiff ℂ ω (fun v : Fin (n * g) → ℂ => colsOf n g v) := by
    unfold colsOf
    fun_prop
  have hΛ : ContDiff ℂ ω (fun x : Fin n → Fin g → ℂ => Λ x) := (LinearMap.toContinuousLinearMap Λ).contDiff
  show ContDiffAt ℂ ω (fun v => Φ.fr j (Λ (colsOf n g v))) 0
  exact han.contDiffAt.comp (x := 0) (hΛ.comp hc).contDiffAt

variable {K : Type} [Fintype K] {φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)}
  {Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}

theorem anO_prod (hφ : ∀ k, Φ.JetMap m (φ k) (Λ k)) (ε : K → ℤ) {j : K → L.L.ι} (h : ⊤ ≤ LB.wchart L.L φ j) :
    AnO fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ ε k := by
  classical
  have hk : ∀ k, ⊤ ≤ φ k ⁻¹ᵁ L.L.U (j k) := fun k x _ => by
    have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
    unfold LB.wchart at hx
    exact Set.mem_iInter.1 hx k
  have hne : ∀ k, Φ.fr (j k) (Λ k (colsOf n g 0)) ≠ 0 := fun k => Φ.fr_ne _ _ (origin_mem Φ (hφ k) (hk k))
  have hfr : ∀ k, AnO fun w => Φ.fr (j k) (Λ k w) := fun k => anO_fr Φ (hφ k) (hk k)
  have key : ∀ s : Finset K,
      ContDiffAt ℂ ω (fun v => ∏ k ∈ s, Φ.fr (j k) (Λ k (colsOf n g v)) ^ ε k) 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.prod_empty]
      exact contDiffAt_const
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact (show ContDiffAt ℂ ω (fun v => Φ.fr (j a) (Λ a (colsOf n g v)) ^ ε a) 0 from
        AnO.zpow (hfr a) (hne a) (ε a)).mul ih
  exact key Finset.univ

theorem prod_ne (hφ : ∀ k, Φ.JetMap m (φ k) (Λ k)) (ε : K → ℤ) {j : K → L.L.ι} (h : ⊤ ≤ LB.wchart L.L φ j) :
    ∏ k, Φ.fr (j k) (Λ k (colsOf n g 0)) ^ ε k ≠ 0 := by
  have hk : ∀ k, ⊤ ≤ φ k ⁻¹ᵁ L.L.U (j k) := fun k x _ => by
    have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
    unfold LB.wchart at hx
    exact Set.mem_iInter.1 hx k
  have hne : ∀ k, Φ.fr (j k) (Λ k (colsOf n g 0)) ≠ 0 := fun k => Φ.fr_ne _ _ (origin_mem Φ (hφ k) (hk k))
  exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)

end

theorem map_res_val {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (h' : ⊤ ≤ V) (u : Γ(X, U)ˣ) :
    (X.presheaf.map (homOfLE h').op).hom (Semi.res h u).val =
      (X.presheaf.map (homOfLE (h'.trans h)).op).hom u.val := by
  unfold Semi.res
  show (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op).hom u.val = _
  rw [← Functor.map_comp]
  rfl

end GlobalTheory.AnVal.JetAlg


open GlobalTheory.AnVal.JetAlg in
set_option backward.isDefEq.respectTransparency false in
theorem GlobalTheory.AnVal.jetRd_mul_inv_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε' : K' → ℤ) (τ' : LB.Gen (LB.LinComb L.L φ' ε')) (Λ' : K' → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m φ' ε' τ' Λ' → Φ.JetRd m (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L.L φ ε φ' ε' τ τ') (Sum.elim Λ Λ') ∧ Φ.JetRd m φ (fun k => -ε k) (LB.invGen L.L φ ε τ) Λ ∧ ∀ p : ℕ, Φ.JetRd m φ (fun k => (p : ℤ) * ε k) ⟨fun j => τ.s j ^ p⟩ Λ := by
  intro S A _ _ L x0 g Φ n m K K' _ _ φ ε τ Λ φ' ε' τ' Λ' h1 h2
  refine ⟨⟨fun k => ?_, fun j h => ?_⟩, ⟨h1.1, fun j h => ?_⟩, fun p => ⟨h1.1, fun j h => ?_⟩⟩
  · cases k with
    | inl k => exact h1.1 k
    | inr k => exact h2.1 k
  · have hL : ⊤ ≤ LB.wchart L.L φ (j ∘ Sum.inl) := fun x _ => by
      have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
      unfold LB.wchart at hx ⊢
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inl k)
    have hR : ⊤ ≤ LB.wchart L.L φ' (j ∘ Sum.inr) := fun x _ => by
      have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
      unfold LB.wchart at hx ⊢
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inr k)
    unfold LB.mulGen
    rw [Units.val_mul, map_mul, map_res_val, map_res_val]
    refine (congrArg₂ (· * ·) (h1.2 (j ∘ Sum.inl) hL) (h2.2 (j ∘ Sum.inr) hR)).trans ?_
    rw [← map_mul, ← jetN_mul m (anO_prod Φ h1.1 ε hL) (anO_prod Φ h2.1 ε' hR)]
    refine congrArg (toΓ _) (congrArg (jetN m) (funext fun w => ?_))
    rw [Fintype.prod_sum_type]
    rfl
  · have e1 : ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom ((τ.s j)⁻¹).val *
        ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom (τ.s j).val = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [h1.2 j h] at e1
    have e2 := jetN_inv_mul m (anO_prod Φ h1.1 ε h) (prod_ne Φ h1.1 ε h)
    have hG : (fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ (-ε k)) = fun w => (∏ k, Φ.fr (j k) (Λ k w) ^ ε k)⁻¹ := by
      funext w
      simp only [zpow_neg, Finset.prod_inv_distrib]
    refine left_inv_eq_right_inv e1 ?_
    rw [mul_comm, ← map_mul]
    beta_reduce
    rw [hG, e2, map_one]
  · have hP : (fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ ((p : ℤ) * ε k)) = fun w => (∏ k, Φ.fr (j k) (Λ k w) ^ ε k) ^ p := by
      funext w
      simp only [mul_comm (p : ℤ), zpow_mul, zpow_natCast, Finset.prod_pow]
    beta_reduce
    rw [hP, jetN_pow m (anO_prod Φ h1.1 ε h) p, map_pow, ← h1.2 j h, ← map_pow, ← Units.val_pow_eq_pow_val]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPoints
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetLinSub

theorem tay_coord {N : ℕ} (k : Fin N) :
    tay (fun v : Fin N → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  classical
  have hθ : ContDiffAt ℂ ω (fun v : Fin N → ℂ => v k) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).contDiff.contDiffAt
  ext n
  by_cases hn : n = 0
  · subst hn
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_tay, TM.mD_zero]
    simp
  · obtain ⟨⟨a, j⟩, hp⟩ : ∃ p, n p ≠ 0 := by
      by_contra hc; push Not at hc; exact hn (Finsupp.ext hc)
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + Finsupp.single ((0 : Fin 1), j) 1 :=
      ⟨n - Finsupp.single ((0 : Fin 1), j) 1, (tsub_add_cancel_of_le
        (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hp))).symm⟩
    have h1 := TM.pderiv_tay hθ j
    have h2 : (fun y : Fin N → ℂ => fderiv ℂ (fun v : Fin N → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j 1 : Fin N → ℂ) k := by
      funext y
      have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).fderiv (x := y)
      exact congrArg (fun T : (Fin N → ℂ) →L[ℂ] ℂ => T (Pi.single j 1)) this
    rw [h2, TM.tay_const] at h1
    have h3 : MvPowerSeries.pderiv (R := ℂ) ((0 : Fin 1), j) (MvPowerSeries.X ((0 : Fin 1), k) :
        MvPowerSeries (Fin 1 × Fin N) ℂ) = MvPowerSeries.C ((Pi.single j 1 : Fin N → ℂ) k) := by
      rw [MvPowerSeries.pderiv_X]
      by_cases h : k = j
      · subst h; simp
      · simp [Prod.ext_iff, h]
    have h4 := congrArg (MvPowerSeries.coeff n') (h1.trans h3.symm)
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv] at h4
    exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero _) h4

theorem psJet_X {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (s : κ) :
    psJet m (MvPowerSeries.X s : MvPowerSeries κ ℂ) = Ideal.Quotient.mk _ (MvPolynomial.X s) := by
  rw [← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem jetOf_coord {N : ℕ} (m : ℕ) (k : Fin N) :
    jetOf m (fun v : Fin N → ℂ => v k) = Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), k)) := by
  rw [jetOf, tay_coord, psJet_X]

def flatL {n n' g : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) :
    (Fin (n' * g) → ℂ) →L[ℂ] (Fin (n * g) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v k => B (colsOf n' g v) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
      map_add' := fun v w => by
        funext k
        have : colsOf n' g (v + w) = colsOf n' g v + colsOf n' g w := rfl
        rw [this, map_add (f := _)]; rfl
      map_smul' := fun c v => by
        funext k
        have : colsOf n' g (c • v) = c • colsOf n' g v := rfl
        rw [this, map_smul]; rfl }

theorem flatL_apply {n n' g : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (v : Fin (n' * g) → ℂ)
    (k : Fin (n * g)) :
    flatL B v k = B (colsOf n' g v) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := rfl

theorem colsOf_flatL {n n' g : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (v : Fin (n' * g) → ℂ) :
    colsOf n g (flatL B v) = B (colsOf n' g v) := by
  funext i j
  show flatL B v (finProdFinEquiv (i, j)) = _
  rw [flatL_apply, Equiv.symm_apply_apply]

theorem subst_renN {n n' g m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (a : Jet ℂ (Fin 1 × Fin (n * g)) m) :
    σ (renN n g m a) = renN n' g m (jetMap (anLin (flatL B)) (anLin_mem _) a) := by
  have key : (σ.comp (renN n g m)).comp (Ideal.Quotient.mkₐ ℂ _) =
      ((renN n' g m).comp (jetMap (m := m) (anLin (flatL B)) (anLin_mem _))).comp (Ideal.Quotient.mkₐ ℂ _) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, k⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    have e1 : renN n g m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), k))) =
        psJet m (MvPowerSeries.X (finProdFinEquiv.symm k)) := by
      rw [psJet_X]
      show Ideal.Quotient.mk _ (MvPolynomial.aeval _ (MvPolynomial.X _)) = _
      rw [MvPolynomial.aeval_X]
    have hθ : ContDiffAt ℂ ω (fun v : Fin (n * g) → ℂ => v k) 0 :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) k).contDiff.contDiffAt
    have e2 := jetOf_comp_anLin m hθ (flatL B)
    rw [jetOf_coord] at e2
    show σ (renN n g m (Ideal.Quotient.mk _ _)) =
      renN n' g m (jetMap (m := m) (anLin (flatL B)) (anLin_mem _) (Ideal.Quotient.mk _ _))
    rw [e1, hσ, ← e2]
    rfl
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact DFunLike.congr_fun key p

theorem subst_jetN {n n' g m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (f : (Fin n → Fin g → ℂ) → ℂ) (hf : ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0) :
    σ (jetN m f) = jetN m (fun w => f (B w)) := by
  rw [jetN, subst_renN B σ hσ, ← jetOf_comp_anLin m hf (flatL B), jetN]
  congr 2
  funext v
  rw [Function.comp_apply, colsOf_flatL]

theorem isHolFam_clm {Y : Scheme.{0}} {N N' : ℕ} (e : (Fin N → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (T : (Fin N' → ℂ) →L[ℂ] (Fin N → ℂ)) : IsHolFam (fun v => e (T v)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hol U f
  exact ⟨h1.preimage T.continuous, h2.comp T.differentiable.differentiableOn fun _ hv => hv⟩

theorem jetPt_clm {Y : Scheme.{0}} {N N' : ℕ} (e : (Fin N → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (T : (Fin N' → ℂ) →L[ℂ] (Fin N → ℂ)) (e' : (Fin N' → ℂ) → (Sp ℂ ⟶ Y)) (hol' : IsHolFam e')
    (he : ∀ v, e' v = e (T v)) (m : ℕ) :
    spMap ((jetMap (anLin T) (anLin_mem T) : Jet ℂ (Fin 1 × Fin N) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin N') m) :
      Jet ℂ (Fin 1 × Fin N) m →+* Jet ℂ (Fin 1 × Fin N') m) ≫ jetPt e hol m = jetPt e' hol' m := by
  obtain rfl : e' = fun v => e (T v) := funext he
  have := isLocalHom_jetMap (K := ℂ) (m := m) (anLin T) (anLin_mem T)
  refine jetPt_precompD _ _ hol hol' (by show e (T 0) = e 0; rw [map_zero]) m _ fun U hU f => ?_
  exact (jetOf_comp_anLin m (contDiffAt_val _ hol hU f) T).symm

set_option backward.isDefEq.respectTransparency false in
theorem spMap_closedPoint {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (f : R →+* R')
    (hf : IsLocalHom f) : spMap f (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R :=
  IsLocalRing.comap_closedPoint f

theorem appTop_toΓ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (a : R) :
    ((spMap f).appTop).hom (toΓ R a) = toΓ R' (f a) := by
  simp only [toΓ, spMap]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem res_pull {Y Z : Scheme.{0}} (s : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens) (h : ⊤ ≤ W) (h' : ⊤ ≤ W')
    (le : W' ≤ s ⁻¹ᵁ W) (x : Γ(Y, W)) :
    (Z.presheaf.map (homOfLE h').op).hom ((Z.presheaf.map (homOfLE le).op).hom ((s.app W).hom x)) =
      s.appTop.hom ((Y.presheaf.map (homOfLE h).op).hom x) := by
  obtain rfl : W = ⊤ := top_le_iff.1 h
  obtain rfl : W' = ⊤ := top_le_iff.1 h'
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  have e1 : Y.presheaf.map (homOfLE h).op = 𝟙 _ := Y.presheaf.map_id _
  have e2 : Z.presheaf.map ((homOfLE le).op ≫ (homOfLE h').op) = 𝟙 _ := Z.presheaf.map_id _
  rw [e1, e2]
  rfl

section Main

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem jetMap_sub {n n' m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : Φ.JetMap m ψ Λ) :
    Φ.JetMap m (spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ ψ) (Λ ∘ₗ B) := by
  obtain ⟨hol, rfl⟩ := h
  have he : ∀ v : Fin (n' * g) → ℂ, (Φ.e ((Λ ∘ₗ B) (colsOf n' g v))).left =
      (Φ.e (Λ (colsOf n g (flatL B v)))).left := fun v => by rw [colsOf_flatL]; rfl
  have hol' : IsHolFam (fun v : Fin (n' * g) → ℂ => (Φ.e ((Λ ∘ₗ B) (colsOf n' g v))).left) := by
    rw [funext he]
    exact isHolFam_clm _ hol (flatL B)
  refine ⟨hol', ?_⟩
  rw [← jetPt_clm _ hol (flatL B) _ hol' he m, ← Category.assoc, ← Category.assoc, ← anSpMap_comp, ← anSpMap_comp]
  congr 2
  exact RingHom.ext fun a => subst_renN B σ hσ a

theorem jetMap_closedPoint {n m : ℕ} (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : Φ.JetMap m ψ Λ) :
    ψ (IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m)) = (Φ.e 0).left PullbackSections.cpt := by
  obtain ⟨hol, rfl⟩ := h
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  refine (congrArg _ (spMap_closedPoint _ (isLocalHom_jetMap _ _))).trans ?_
  refine (jetPt_closedPoint _ hol m).trans ?_
  have : Λ (colsOf n g 0) = 0 := map_zero Λ
  simp only [this]

theorem contDiffAt_fr {n : ℕ} (j : L.L.ι) (hj : (Φ.e 0).left PullbackSections.cpt ∈ L.L.U j) (a : ℤ)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    ContDiffAt ℂ ω (fun v : Fin (n * g) → ℂ => Φ.fr j (Λ (colsOf n g v)) ^ a) 0 := by
  have h0 := top_le_of_mem hj
  have h1 : AnalyticAt ℂ (Φ.fr j) 0 :=
    ReciprocityTheory.AnForm.Osgood.osgood g _ _ (Φ.hol (L.L.U j) 0).1 (Φ.fr_hol j) 0 h0
  have h2 : AnalyticAt ℂ (fun z => Φ.fr j z ^ a) 0 := h1.fun_zpow (Φ.fr_ne j 0 h0)
  let T : (Fin (n * g) → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap
    (Λ ∘ₗ { toFun := colsOf n g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
  have h3 : AnalyticAt ℂ (fun z => Φ.fr j z ^ a) (T 0) := by rw [map_zero]; exact h2
  exact (h3.comp (T.analyticAt 0)).contDiffAt

theorem jetRd_sub {n n' m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    {K : Type} [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ)
    (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : Φ.JetRd m φ ε τ Λ) :
    Φ.JetRd m (fun k => spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ φ k) ε
      (LB.pullGen L.L φ ε τ (spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m)))
      (fun k => Λ k ∘ₗ B) := by
  obtain ⟨h1, h2⟩ := h
  have h1' := fun k => jetMap_sub Φ B σ hσ (φ k) (Λ k) (h1 k)
  refine ⟨h1', fun j hj => ?_⟩
  have hU : ∀ k, (Φ.e 0).left PullbackSections.cpt ∈ L.L.U (j k) := fun k => by
    rw [← jetMap_closedPoint Φ _ _ (h1' k)]
    exact (hj.trans (LB.wchart_le _ _ j k)) (Set.mem_univ _)
  have hj0 : ⊤ ≤ LB.wchart L.L φ j := by
    intro y _
    refine Set.mem_iInter.2 fun k => ?_
    have hk : φ k (IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m)) ∈ L.L.U (j k) := by
      rw [jetMap_closedPoint Φ _ _ (h1 k)]; exact hU k
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of (Jet ℂ (Fin n × Fin g) m)) (φ k) hk).ge
      (Set.mem_univ y)
  refine (res_pull _ _ _ hj0 hj _ (τ.s j).val).trans ?_
  rw [h2 j hj0, appTop_toΓ]
  congr 1
  exact subst_jetN B σ hσ _ (contDiffAt_prod fun k _ => contDiffAt_fr Φ (j k) (hU k) (ε k) (Λ k))

end Main

theorem jetRd_linSubst : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n n' m : ℕ) (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (sb : Fin n × Fin g → MvPolynomial (Fin n' × Fin g) ℂ), (∀ p, (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m) (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2)) → ∀ (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m (fun k => spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ φ k) ε (LB.pullGen L.L φ ε τ (spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m))) (fun k => Λ k ∘ₗ B) := by
  intro S A _ _ L x0 g Φ n n' m B sb hsb K _ φ ε τ Λ h
  exact jetRd_sub Φ B (jetSubstP m sb) hsb φ ε τ Λ h

end GlobalTheory.JetLinSub
end
end

