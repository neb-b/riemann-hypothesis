module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT

theorem objMap_comp : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : Obj b N s₁) (o₂ : Obj b N s₂) (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → Nonempty (ObjMap o₁ o₃ (f ≫ g)) := by
  intro p _ D R _ b N S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g h₁ h₂
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherDegreeClassDiesOnFinerEtaleNeighbourhood
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section
namespace GlobalTheory.KillFiner

theorem pull_spMap_comp (q : ℕ) {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (ρ : R →+* S) (ψ : S →+* T)
    (n i : ℤ) (z : Ht q (sp R) n i) :
    pull _ (spMap (ψ.comp ρ)) _ _ z = pull _ (spMap ψ) _ _ (pull _ (spMap ρ) _ _ z) := by
  have e : spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ := by
    show sch.map (Spec.map (CommRingCat.ofHom (ψ.comp ρ))) = sch.map (Spec.map (CommRingCat.ofHom ψ)) ≫ sch.map (Spec.map (CommRingCat.ofHom ρ))
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]
  rw [e, pull_comp]

theorem main : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsNbhd B A' f → ∀ (m i : ℤ), 2 ≤ m → ∀ z : Ht q (sp (Localization.Away (algebraMap B A' f))) m i, ∃ (A'' : Type) (_ : CommRing A'') (_ : Algebra B A'') (_ : Algebra.Etale B A'') (φ : A' →ₐ[B] A''), IsNbhd B A'' f ∧ pull _ (spMap (awayHom φ f)) _ _ z = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf hfu A' _ _ _ hN
  set f' : A' := algebraMap B A' f with hf'
  intro m i hm z
  set R := Localization.Away f'
  have hBf : ¬ IsField B := fun hB => hfu (by
    letI := hB.toField; exact isUnit_iff_ne_zero.mpr hf)
  have hqR : IsUnit (q : R) := by
    have := ((hq.map (algebraMap k B)).map (algebraMap B A')).map (algebraMap A' R)
    simpa only [map_natCast] using this

  have hFR : Subsingleton (Ht q (sp (FractionRing R)) m i) := by
    obtain ⟨hArt, hRed⟩ := GlobalTheory.T.fractionRing_away_etale_dedekind_artinian_reduced B f A'
    refine GlobalTheory.T.cohomology_vanishes_artinian q _ m i (fun M => ?_)
    obtain ⟨alg, halg⟩ := GlobalTheory.T.etale_maximal_quotient_algebraic k B hBf f hf A' M
    have hqM : IsUnit (q : FractionRing R ⧸ M.asIdeal) := by
      have := (hqR.map (algebraMap R (FractionRing R))).map (Ideal.Quotient.mk M.asIdeal)
      rwa [map_natCast, map_natCast] at this
    haveI := M.isMaximal
    letI : Field (FractionRing R ⧸ M.asIdeal) := Ideal.Quotient.field _
    exact GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing R ⧸ M.asIdeal) hqM m i hm

  obtain ⟨g, hg, hz⟩ := GlobalTheory.T.class_vanishes_away_nonZeroDivisor q R hqR m i z (Subsingleton.elim _ _)

  have hf'reg : IsSMulRegular A' f' := by
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := A') (mem_nonZeroDivisors_of_ne_zero hf)
    intro x y hxy
    apply h
    simpa [Algebra.smul_def, hf'] using hxy
  have hpow : ∀ (N : ℕ) (y : A'), f' ^ N * y = 0 → y = 0 := by
    intro N y hy
    induction N generalizing y with
    | zero => simpa using hy
    | succ N ih =>
      apply ih
      apply hf'reg
      simp only [smul_eq_mul, mul_zero]
      rw [← hy]; ring

  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f') g
  simp only at hs
  have ha : a ∈ nonZeroDivisors A' := by
    suffices key : ∀ y : A', y * a = 0 → y = 0 from
      mem_nonZeroDivisors_iff.mpr ⟨fun y hy => key y (by rw [mul_comm]; exact hy), key⟩
    intro y hy
    have h1 : algebraMap A' R y * g = 0 := by
      have hsu : IsUnit (algebraMap A' R (s : A')) := IsLocalization.map_units R s
      apply hsu.mul_left_injective
      simp only [zero_mul]
      rw [mul_assoc, hs, ← map_mul, hy, map_zero]
    have h2 : algebraMap A' R y = 0 := (mem_nonZeroDivisors_iff.mp hg).2 _ h1
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f')] at h2
    obtain ⟨⟨c, N, rfl⟩, hc⟩ := h2
    exact hpow N y hc

  let J : Ideal A' :=
    { carrier := {x | ∃ N : ℕ, a ∣ x * f' ^ N}
      add_mem' := by
        rintro x y ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
        refine ⟨N₁ + N₂, ?_⟩
        have e : (x + y) * f' ^ (N₁ + N₂) = (x * f' ^ N₁) * f' ^ N₂ + (y * f' ^ N₂) * f' ^ N₁ := by ring
        rw [e]
        exact dvd_add (h₁.mul_right _) (h₂.mul_right _)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨N, h⟩
        refine ⟨N, ?_⟩
        rw [smul_eq_mul, mul_assoc]
        exact h.mul_left c }
  have hJ : J ⊔ Ideal.span {f'} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hfM : f' ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    obtain ⟨t, htM, N, hN⟩ := GlobalTheory.T.exists_dvd_mul_pow_etale_nbhd_zeroLocus B A' f hf hN a ha M hM hfM
    exact htM (hle (Ideal.mem_sup_left ⟨N, hN⟩))
  have h1 : (1 : A') ∈ J ⊔ Ideal.span {f'} := by rw [hJ]; trivial
  obtain ⟨h, ⟨N, hhN⟩, y, hy, hhy⟩ := Submodule.mem_sup.mp h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy

  refine ⟨Localization.Away h, inferInstance, inferInstance, inferInstance,
    IsScalarTower.toAlgHom B A' (Localization.Away h), GlobalTheory.T.isNbhd_away_of_add_algebraMap_mul_eq_one B A' f h c hN (by rw [← hhy]; ring), ?_⟩
  set φ := IsScalarTower.toAlgHom B A' (Localization.Away h)
  set S := Localization.Away (algebraMap B (Localization.Away h) f)
  have hcomp : ∀ x : A', awayHom φ f (algebraMap A' R x) = algebraMap _ S (φ x) := fun x =>
    RingHom.congr_fun (awayHom_comp_algebraMap φ f) x
  have hfS : IsUnit (algebraMap _ S (φ f')) := by
    rw [hf', AlgHom.commutes]; exact IsLocalization.Away.algebraMap_isUnit _
  have hhS : IsUnit (algebraMap _ S (φ h)) :=
    (IsLocalization.Away.algebraMap_isUnit h).map (algebraMap _ S)
  have haS : IsUnit (algebraMap _ S (φ a)) := by
    apply isUnit_of_dvd_unit (y := algebraMap _ S (φ (h * f' ^ N)))
    · exact map_dvd _ (map_dvd _ hhN)
    · rw [map_mul, map_pow, map_mul, map_pow]; exact hhS.mul (hfS.pow N)
  have hgS : IsUnit (awayHom φ f g) := by
    have e : awayHom φ f g * awayHom φ f (algebraMap A' R s) = algebraMap _ S (φ a) := by
      rw [← map_mul, hs, hcomp]
    rw [← e] at haS
    exact isUnit_of_mul_isUnit_left haS
  have hfac : (IsLocalization.Away.lift g hgS).comp (algebraMap R (Localization.Away g)) = awayHom φ f :=
    IsLocalization.Away.lift_comp g hgS
  rw [← hfac, pull_spMap_comp, hz, map_zero]
end GlobalTheory.KillFiner
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFamilyConjConstant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

namespace HolConj

variable {J : Type} [Fintype J] [DecidableEq J] {d : J → ℕ}

def unit (j : J) (p q : Fin (d j)) : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ :=
  Pi.single j (Matrix.single p q 1)

lemma pi_single_mul_ne {R : J → Type} [∀ i, MulZeroClass (R i)] {i j : J} (h : i ≠ j)
    (x : R i) (y : R j) : (Pi.single i x : Π k, R k) * Pi.single j y = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [Pi.single_apply, Ne.symm h]
  · simp [Pi.single_apply, hk]

lemma unit_mul_ne_factor {j j' : J} (h : j ≠ j') (p q : Fin (d j)) (p' q' : Fin (d j')) :
    unit (d := d) j p q * unit j' p' q' = 0 :=
  pi_single_mul_ne h _ _

lemma unit_mul_same (j : J) (p q r : Fin (d j)) :
    unit (d := d) j p q * unit j q r = unit j p r := by
  simp only [unit, ← Pi.single_mul, Matrix.single_mul_single_same, _root_.mul_one]

lemma unit_mul_ne (j : J) (p q p' r : Fin (d j)) (h : q ≠ p') :
    unit (d := d) j p q * unit j p' r = 0 := by
  simp only [unit, ← Pi.single_mul, Matrix.single_mul_single_of_ne _ _ _ _ h, Pi.single_zero]

lemma pi_single_sum {R : J → Type} [∀ i, AddCommMonoid (R i)] {X : Type} (s : Finset X)
    (j : J) (f : X → R j) :
    (Pi.single j (∑ x ∈ s, f x) : Π k, R k) = ∑ x ∈ s, Pi.single j (f x) :=
  map_sum (AddMonoidHom.single R j) f s

lemma sum_unit_diag : ∑ j, ∑ k, unit (d := d) j k k = 1 := by
  simp only [unit]
  have : ∀ j, ∑ k, (Pi.single j (Matrix.single k k (1:ℂ)) : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
      = Pi.single j 1 := by
    intro j
    rw [← Matrix.sum_single_one, pi_single_sum]
  simp only [this]
  exact Finset.univ_sum_single (fun j => (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ))

lemma eq_sum_unit (t : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    t = ∑ j, ∑ p, ∑ q, t j p q • unit j p q := by
  conv_lhs => rw [← Finset.univ_sum_single t]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Matrix.matrix_eq_sum_single (t j)]
  simp only [unit, pi_single_sum, ← Pi.single_smul, Matrix.smul_single, smul_eq_mul, _root_.mul_one]

end HolConj

end GlobalTheory

namespace GlobalTheory

namespace HolConj

variable {J : Type} [Fintype J] [DecidableEq J] {d : J → ℕ} [∀ j, NeZero (d j)]
variable {A : Type} [Ring A] [Algebra ℂ A]

def conjMat (f g : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A) : A :=
  ∑ j, ∑ k, f (unit j k 0) * g (unit j 0 k)

lemma conjMat_self (f : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A) :
    conjMat f f = 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [conjMat, ← map_mul, unit_mul_same, ← map_sum, sum_unit_diag, map_one]

lemma conjMat_unit (f g : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A)
    (j' : J) (p q : Fin (d j')) :
    f (unit j' p q) * conjMat f g = conjMat f g * g (unit j' p q) := by
  have hL : f (unit j' p q) * conjMat f g = f (unit j' p 0) * g (unit j' 0 q) := by
    simp only [conjMat, Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_eq_single j']
    · rw [Finset.sum_eq_single q]
      · rw [unit_mul_same]
      · intro k _ hk
        rw [unit_mul_ne _ _ _ _ _ (Ne.symm hk), map_zero, zero_mul]
      · simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [unit_mul_ne_factor (Ne.symm hj), map_zero, zero_mul]
    · simp
  have hR : conjMat f g * g (unit j' p q) = f (unit j' p 0) * g (unit j' 0 q) := by
    simp only [conjMat, Finset.sum_mul, _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_eq_single j']
    · rw [Finset.sum_eq_single p]
      · rw [unit_mul_same]
      · intro k _ hk
        rw [unit_mul_ne _ _ _ _ _ hk, map_zero, mul_zero]
      · simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [unit_mul_ne_factor hj, map_zero, mul_zero]
    · simp
  rw [hL, hR]

lemma conjMat_intertwines (f g : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A)
    (t : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    f t * conjMat f g = conjMat f g * g t := by
  rw [eq_sum_unit t]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    conjMat_unit]

end HolConj

theorem holFamily_conj_const : ∀ (S : Type) [Ring S] [Algebra ℂ S] [FiniteDimensional ℂ S] [IsSemisimpleRing S] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (S →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ)), IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → ∃ (B' : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h b) ∧ ∀ a, F b a * h b = h b * F b₀ a := by
  intro S _ _ _ _ g m B b₀ F hB hb₀ hF
  obtain ⟨n, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ S
  let f : (Fin m → ℂ) →
      ((Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) :=
    fun b => (F b).comp e.symm.toAlgHom
  let h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => HolConj.conjMat (f b) (f b₀)
  have hdiff : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B := by
    intro i j
    simp only [h, f, HolConj.conjMat, Matrix.sum_apply, Matrix.mul_apply, AlgHom.comp_apply]
    refine DifferentiableOn.fun_sum fun _ _ => DifferentiableOn.fun_sum fun _ _ =>
      DifferentiableOn.fun_sum fun _ _ => (hF _ _ _).mul_const _
  have hc : ContinuousOn h B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hdiff i j).continuousOn
  have hdet : ContinuousOn (fun b => (h b).det) B :=
    (continuous_id.matrix_det).comp_continuousOn hc
  have h₀ : h b₀ = 1 := HolConj.conjMat_self _
  refine ⟨B ∩ (fun b => (h b).det) ⁻¹' {0}ᶜ, h,
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton, ⟨hb₀, by simp [h₀]⟩,
    Set.inter_subset_left, h₀, fun i j => (hdiff i j).mono Set.inter_subset_left, ?_⟩
  rintro b ⟨-, hb⟩
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hb), fun a => ?_⟩
  have := HolConj.conjMat_intertwines (f b) (f b₀) (e a)
  simpa [f] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.HeckeOrthSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

open Module.End
open scoped InnerProductSpace

variable {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem iSup_iInf_eigenspace_eq_top [FiniteDimensional ℂ E] (T : I → E →ₗ[ℂ] E) (hc : ∀ i k, Commute (T i) (T k))
    (hadj : ∀ i, ∃ k, ∀ x y, ⟪T i x, y⟫_ℂ = ⟪x, T k y⟫_ℂ) :
    ⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i) = ⊤ := by
  choose s hs using hadj
  have hs' : ∀ i x y, ⟪T (s i) x, y⟫_ℂ = ⟪x, T i y⟫_ℂ := fun i x y => by
    rw [← inner_conj_symm, ← hs, inner_conj_symm]
  let H : I ⊕ I → E →ₗ[ℂ] E := Sum.elim (fun i => T i + T (s i)) (fun i => Complex.I • (T i - T (s i)))
  have hH : ∀ i, (H i).IsSymmetric := by
    rintro (i | i) x y
    · simp only [H, Sum.elim_inl, LinearMap.add_apply, inner_add_left, inner_add_right, hs i, hs' i]
      ring
    · simp only [H, Sum.elim_inr, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
        inner_sub_left, inner_sub_right, hs i, hs' i, Complex.conj_I]
      ring
  have hT : ∀ i k, Commute (H i) (T k) := by
    rintro (i | i) k
    · exact (hc _ _).add_left (hc _ _)
    · exact ((hc _ _).sub_left (hc _ _)).smul_left _
  have hHc : ∀ i k, Commute (H i) (H k) := by
    rintro i (k | k)
    · exact (hT _ _).add_right (hT _ _)
    · exact ((hT _ _).sub_right (hT _ _)).smul_right _
  have h := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hH (fun i k _ => hHc i k)
  rw [eq_top_iff, ← h]
  refine iSup_le fun χ => le_iSup_of_le (fun i => (χ (.inl i) - Complex.I * χ (.inr i)) / 2) fun x hx => ?_
  simp only [Submodule.mem_iInf, mem_eigenspace_iff] at hx ⊢
  intro i
  have h1 : T i x + T (s i) x = χ (.inl i) • x := hx (.inl i)
  have h2 : Complex.I • (T i x - T (s i) x) = χ (.inr i) • x := hx (.inr i)
  have h3 : T i x - T (s i) x = -(Complex.I * χ (.inr i)) • x := by
    rw [neg_smul, mul_smul, ← h2, smul_smul, Complex.I_mul_I]; simp
  have h4 : (2 : ℂ) • T i x = (χ (.inl i) - Complex.I * χ (.inr i)) • x := by
    rw [sub_eq_add_neg, add_smul, ← h1, ← h3, two_smul]; abel
  rw [div_eq_inv_mul, mul_smul, ← h4, smul_smul]; simp

end Abstract

section Form

variable {X I : Type} [AddCommGroup X] [Module ℂ X]

structure IsPosOn (Y : Submodule ℂ X) (B : X → X → ℂ) : Prop where
  lin : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z
  symm : ∀ x ∈ Y, ∀ y ∈ Y, B y x = star (B x y)
  pos : ∀ x ∈ Y, x ≠ 0 → 0 < (B x x).re

variable {Y : Submodule ℂ X} {B : X → X → ℂ}

theorem IsPosOn.zero_right (h : IsPosOn Y B) {x : X} (hx : x ∈ Y) : B x 0 = 0 := by
  have := h.lin x hx 0 Y.zero_mem 0 Y.zero_mem 1
  simpa using this

theorem IsPosOn.add_right (h : IsPosOn Y B) {x y z : X} (hx : x ∈ Y) (hy : y ∈ Y) (hz : z ∈ Y) :
    B x (y + z) = B x y + B x z := by
  simpa using h.lin x hx y hy z hz 1

theorem IsPosOn.smul_right (h : IsPosOn Y B) {x z : X} (hx : x ∈ Y) (hz : z ∈ Y) (c : ℂ) :
    B x (c • z) = c * B x z := by
  simpa [h.zero_right hx] using h.lin x hx 0 Y.zero_mem z hz c

@[reducible] def IsPosOn.core (h : IsPosOn Y B) : InnerProductSpace.Core ℂ Y where
  inner x y := B x y
  conj_inner_symm x y := (h.symm y y.2 x x.2).symm
  re_inner_nonneg x := by
    by_cases hx : (x : X) = 0
    · show 0 ≤ (B x x).re
      rw [hx, h.zero_right Y.zero_mem]; simp
    · exact (h.pos x x.2 hx).le
  add_left x y z := by
    show B ((x : X) + y) z = B x z + B y z
    rw [h.symm z z.2 _ (Y.add_mem x.2 y.2), h.add_right z.2 x.2 y.2, h.symm z z.2 x x.2, h.symm z z.2 y y.2, star_add]
  smul_left x y r := by
    show B (r • (x : X)) y = starRingEnd ℂ r * B x y
    rw [h.symm y y.2 _ (Y.smul_mem r x.2), h.smul_right y.2 x.2, h.symm y y.2 x x.2, star_mul']
    rfl
  definite x hx := by
    by_contra h0
    have := h.pos x x.2 (fun e => h0 (Subtype.ext e))
    have hx' : B x x = 0 := hx
    rw [hx'] at this
    simp at this

theorem IsPosOn.le_iSup_eigen [FiniteDimensional ℂ Y] (h : IsPosOn Y B) (T : I → X →ₗ[ℂ] X)
    (hT : ∀ i, ∀ x ∈ Y, T i x ∈ Y) (hc : ∀ i k, ∀ x ∈ Y, T i (T k x) = T k (T i x))
    (hadj : ∀ i, ∃ k, ∀ x ∈ Y, ∀ y ∈ Y, B (T i x) y = B x (T k y))
    (Z : Submodule ℂ X) (hZ : ∀ (χ : I → ℂ), ∀ x ∈ Y, (∀ i, T i x = χ i • x) → x ∈ Z) : Y ≤ Z := by
  letI := h.core
  letI : NormedAddCommGroup Y := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ Y := InnerProductSpace.ofCore _
  have key := iSup_iInf_eigenspace_eq_top (E := Y) (fun i => (T i).restrict (hT i))
    (fun i k => LinearMap.ext fun x => Subtype.ext (hc i k x x.2))
    (fun i => (hadj i).imp fun k hk x y => hk x x.2 y y.2)
  have : (⊤ : Submodule ℂ Y) ≤ Z.comap Y.subtype := by
    rw [← key]
    refine iSup_le fun χ x hx => hZ χ x x.2 fun i => ?_
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx
    exact congrArg Subtype.val (hx i)
  exact fun x hx => this (x := ⟨x, hx⟩) Submodule.mem_top

end Form

section Local

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
  (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
  (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))

variable {θ V S M J χ Sb e}

end Local

end GlobalTheory.HeckeOrthSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackOfGroupSchemeModelBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem exists_isGrpPullback_of_isModel : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], GlobalTheory.SS.IsModel (L := L) A G → ∀ (A' : Over (Sp L)) [GrpObj A'] (ψ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap (algebraMap K L)) ψ → ∃ φ : A'.left ⟶ G.left, IsGrpPullback A' G (spMap (algebraMap W L)) φ := by
  intro K W L _ _ _ _ _ A _ G _ hM A' _ ψ hψ
  obtain ⟨e, he⟩ := hM
  obtain ⟨e₁, he₁, -⟩ := grpPullback_iso hψ (isGrpPullback_pullback A (spMap (algebraMap K L)))
  have : IsMonHom (e₁ ≪≫ e.symm).hom := inferInstanceAs (IsMonHom (e₁.hom ≫ e.inv))
  have h := (isGrpPullback_of_iso (e₁ ≪≫ e.symm)).comp (isGrpPullback_pullback G (spMap (algebraMap W L)))
  exact ⟨_, h.congr (Category.id_comp _) rfl⟩

end GlobalTheory.SS
end

