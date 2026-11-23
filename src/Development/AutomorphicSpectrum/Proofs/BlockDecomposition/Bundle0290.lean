module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0145
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0267
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0280
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0007
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0281
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PderivComp1PtZeroEqZero
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.OntoFirstChernCocycle

section Ring

variable {B : Type} [CommRing B] (a b : Ideal B)

theorem inv_sub_mem {z m : B} (hzm : z * m = 1) (hz : z - 1 ∈ a) : m - 1 ∈ a := by
  have : m - 1 = -((z - 1) * m) := by linear_combination hzm
  rw [this]
  exact neg_mem (a.mul_mem_right _ hz)

theorem log3 (hab : ∀ x y, x ∈ a → y ∈ a → x * y ∈ b) {x y z m : B} (hzm : z * m = 1) (hx : x - 1 ∈ a)
    (hy : y - 1 ∈ a) (hz : z - 1 ∈ a) : x * y * m - 1 - ((y - 1) - (z - 1) + (x - 1)) ∈ b := by
  have hm := inv_sub_mem a hzm hz
  have e : x * y * m - 1 - ((y - 1) - (z - 1) + (x - 1)) =
      (x - 1) * (y - 1) + (-((z - 1) * (m - 1))) + (x - 1) * (m - 1) + (y - 1) * (m - 1) +
        (x - 1) * ((y - 1) * (m - 1)) := by
    linear_combination hzm
  rw [e]
  exact add_mem (add_mem (add_mem (add_mem (hab _ _ hx hy) (neg_mem (hab _ _ hz hm))) (hab _ _ hx hm)) (hab _ _ hy hm))
    (b.mul_mem_left _ (hab _ _ hy hm))

theorem form_key (hab : ∀ x y, x ∈ a → y ∈ a → x * y ∈ b) {W W' Wi t ti c m u e g : B}
    (hW : W = W' * (t * m)) (hWi : W' * Wi = 1) (hti : t * ti = 1) (hcm : c * m = 1)
    (h1 : W - 1 ∈ a) (h2 : W' - 1 ∈ a) (h3 : t * u - 1 ∈ a) (h4 : c * e - 1 ∈ a) (h5 : g + t ∈ a) :
    u - e ∈ a ∧ (W - 1) - (W' - 1) - ((t * u - 1) - (c * e - 1)) - g * (u - e) ∈ b := by
  have hy : t * m - 1 ∈ a := by
    have : t * m - 1 = ((W - 1) - (W' - 1)) * Wi := by
      rw [hW]; linear_combination (1 - t * m) * hWi
    rw [this]
    exact a.mul_mem_right _ (sub_mem h1 h2)
  have hD : u - e ∈ a := by
    have : u - e = ti * ((t * u - 1) - (t * m - 1) - (t * m) * (c * e - 1)) := by
      linear_combination (e - u) * hti + (e * t * ti) * hcm
    rw [this]
    refine a.mul_mem_left _ (sub_mem (sub_mem h3 hy) (a.mul_mem_left _ h4))
  refine ⟨hD, ?_⟩
  have e1 : (W - 1) - (W' - 1) - ((t * u - 1) - (c * e - 1)) - g * (u - e) =
      (W' - 1) * (t * m - 1) + (-((t * m - 1) * (c * e - 1))) + (-((g + t) * (u - e))) := by
    rw [hW]
    linear_combination (t * e) * hcm
  rw [e1]
  exact add_mem (add_mem (hab _ _ h2 hy) (neg_mem (hab _ _ hy h4))) (neg_mem (hab _ _ h5 hD))

end Ring

section Cat

universe v u

variable {R : Type} [CommRing R] {E : Type u} [Category.{v} E] {H : E ⥤ CommAlgCat.{0} R} (a b : IdF H)

def mu {c c' : E} (φ : c ⟶ c') : (H.obj c)ˣ →* (H.obj c')ˣ := Units.map ((H.map φ).hom : H.obj c →* H.obj c')

def dl (W : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ)
    (hW : ∀ {c c' : E} (φ : c ⟶ c'), ((W φ : (H.obj c')ˣ) : H.obj c') - 1 ∈ a.S c') : CH.Cn (sq a b) 1 :=
  fun s => sqMk a b (((W (s.map' 0 1) : (H.obj (s.obj (Fin.last 1)))ˣ) : H.obj (s.obj (Fin.last 1))) - 1) (hW (s.map' 0 1))

def c0 (x : ∀ c, H.obj c) (hx : ∀ c, x c ∈ a.S c) : CH.Cn (sq a b) 0 := fun s => sqMk a b (x _) (hx _)

theorem map_id_sq {T : E} (ρ : T ⟶ T) (h : ρ = 𝟙 T) (x : sqM a b T) : ((sq a b).map ρ).hom x = x := by
  subst h
  simp

theorem sum3 {T : E} {p q r t : H.obj T} (hp : p ∈ a.S T) (hq : q ∈ a.S T) (hr : r ∈ a.S T) (ht : t ∈ a.S T)
    (h : t - ((p - q) + r) ∈ b.S T) :
    (-1 : ℤ) ^ ((0 : Fin 3) : ℕ) • sqMk a b p hp + (-1 : ℤ) ^ ((1 : Fin 3) : ℕ) • sqMk a b q hq +
      (-1 : ℤ) ^ ((2 : Fin 3) : ℕ) • sqMk a b r hr = sqMk a b t ht := by
  have e2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  have e1 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have e0 : ((0 : Fin 3) : ℕ) = 0 := rfl
  rw [e0, e1, e2, pow_zero, pow_one, show (-1 : ℤ) ^ 2 = 1 by norm_num, one_smul, one_smul, neg_one_smul]
  have : sqMk a b p hp + -sqMk a b q hq + sqMk a b r hr = sqMk a b ((p - q) + r) (add_mem (sub_mem hp hq) hr) :=
    Subtype.ext (show Ideal.Quotient.mk (b.S T) p + -Ideal.Quotient.mk (b.S T) q + Ideal.Quotient.mk (b.S T) r = Ideal.Quotient.mk (b.S T) ((p - q) + r) by
      rw [map_add (f := _), map_sub]; ring)
  rw [this]
  exact ((sq_eq a b _ _).2 (by
    have := neg_mem h
    rwa [neg_sub] at this))

def rU (W : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ) (s : ComposableArrows E 2) : (H.obj (s.obj (Fin.last 2)))ˣ :=
  mu (s.map' 1 2) (W (s.map' 0 1)) * W (s.map' 1 2) * (W (s.map' 0 2))⁻¹

theorem d_dl (hab : ∀ T x y, x ∈ a.S T → y ∈ a.S T → x * y ∈ b.S T) (W : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ)
    (hW : ∀ {c c' : E} (φ : c ⟶ c'), ((W φ : (H.obj c')ˣ) : H.obj c') - 1 ∈ a.S c') (s : ComposableArrows E 2)
    (hr : (rU W s : H.obj (s.obj (Fin.last 2))) - 1 ∈ a.S _) :
    CH.d (sq a b) 1 (dl a b W hW) s = sqMk a b ((rU W s : H.obj (s.obj (Fin.last 2))) - 1) hr := by
  change ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (toLast i s)).hom (dl a b W hW (face i s)) = _
  rw [Fin.sum_univ_three]
  have t0 := map_id_sq a b (T := s.obj (Fin.last 2)) (toLast 0 s) (s.map_id _) (dl a b W hW (face 0 s))
  have t1 := map_id_sq a b (T := s.obj (Fin.last 2)) (toLast 1 s) (s.map_id _) (dl a b W hW (face 1 s))
  erw [t0, t1]
  have hx : (H.map (s.map' 1 2)).hom ((W (s.map' 0 1) : H.obj _) - 1) ∈ a.S _ := a.map_mem (s.map' 1 2) (hW (s.map' 0 1))
  have t2 : ((sq a b).map (toLast 2 s)).hom (dl a b W hW (face 2 s)) = sqMk a b _ hx := rfl
  erw [t2]
  refine sum3 a b (hW (s.map' 1 2)) (hW (s.map' 0 2)) hx hr ?_
  have e : (H.map (s.map' 1 2)).hom ((W (s.map' 0 1) : H.obj _) - 1) =
      Units.val (mu (s.map' 1 2) (W (s.map' 0 1))) - 1 := by
    rw [map_sub, map_one]; rfl
  have hx' : Units.val (mu (s.map' 1 2) (W (s.map' 0 1))) - 1 ∈ a.S (s.obj (Fin.last 2)) := e ▸ hx
  have key := log3 (a.S (s.obj (Fin.last 2))) (b.S _) (hab _) (Units.mul_inv (W (s.map' 0 2))) hx' (hW (s.map' 1 2)) (hW (s.map' 0 2))
  rw [e]
  exact key

def mv (s : ComposableArrows E 1) (y : H.obj (s.obj 0)) : H.obj (s.obj (Fin.last 1)) := (H.map (s.map' 0 1)).hom y

theorem pderiv_comp1_pt_zero_eq_zero (x : ∀ c, H.obj c) (hx : ∀ c, x c ∈ a.S c) (s : ComposableArrows E 1)
    (hm : x (s.obj (Fin.last 1)) - mv s (x (s.obj 0)) ∈ a.S _) :
    CH.d (sq a b) 0 (c0 a b x hx) s = sqMk a b (x (s.obj (Fin.last 1)) - mv s (x (s.obj 0))) hm := by
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (toLast i s)).hom (c0 a b x hx (face i s)) = _
  rw [Fin.sum_univ_two]
  have t0 := map_id_sq a b (T := s.obj (Fin.last 1)) (toLast 0 s) (s.map_id _) (c0 a b x hx (face 0 s))
  erw [t0]
  have e1 : ((1 : Fin 2) : ℕ) = 1 := rfl
  have e0 : ((0 : Fin 2) : ℕ) = 0 := rfl
  rw [e0, e1, pow_zero, pow_one, one_smul, neg_one_smul]
  exact Subtype.ext (show Ideal.Quotient.mk _ _ + -Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ by
    rw [map_sub, sub_eq_add_neg]; rfl)

theorem rep_of (x : CH.Cn (sq a b) 1) (hx : CH.d (sq a b) 1 x = 0) (j : CH.Cn (sq a b) 0)
    (z : ∀ s : ComposableArrows E 1, H.obj (s.obj (Fin.last 1)))
    (h : ∀ s, (show sqM a b _ from (x - CH.d (sq a b) 0 j) s).1 = Ideal.Quotient.mk _ (z s)) :
    Rep a b z ((CH.cx (sq a b)).cls x hx) := by
  have hf : CH.d (sq a b) 1 (x - CH.d (sq a b) 0 j) = 0 := by
    rw [map_sub, hx, CH.d_d, sub_zero]
  refine ⟨x - CH.d (sq a b) 0 j, hf, ?_, h⟩
  refine (Submodule.Quotient.eq _).2 ?_
  change x - (x - CH.d (sq a b) 0 j) ∈ LinearMap.range (CH.d (sq a b) 0)
  exact ⟨j, by abel⟩

theorem cls_eq_d {F : E ⥤ ModuleCat.{0} R} {x y : CH.Cn F 2} (hx : CH.d F 2 x = 0) (hy : CH.d F 2 y = 0)
    (h : (CH.cx F).cls x hx = (CH.cx F).cls y hy) : ∃ c : CH.Cn F 1, CH.d F 1 c = x - y := by
  obtain ⟨c, hc⟩ := (Submodule.Quotient.eq _).1 h
  exact ⟨c, hc⟩

end Cat

section Cat2

universe v u

variable {R : Type} [CommRing R] {E : Type u} [Category.{v} E] {H : E ⥤ CommAlgCat.{0} R} (a b : IdF H)

theorem mu_comp {c₀ c₁ c₂ : E} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) (x : (H.obj c₀)ˣ) : mu (f ≫ g) x = mu g (mu f x) := by
  ext
  change (H.map (f ≫ g)).hom _ = (H.map g).hom ((H.map f).hom _)
  rw [H.map_comp]
  rfl

def tw (w : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ) (t : ∀ c, (H.obj c)ˣ) {c c' : E} (φ : c ⟶ c') : (H.obj c')ˣ :=
  w φ * (t c' * (mu φ (t c))⁻¹)

theorem tw_units {G : Type} [CommGroup G] (x y z p q r : G) :
    (x * (p * r⁻¹)) * (y * (q * p⁻¹)) * (z * (q * r⁻¹))⁻¹ = x * y * z⁻¹ := by
  simp only [mul_inv, inv_inv]
  have : x * (p * r⁻¹) * (y * (q * p⁻¹)) * (z⁻¹ * (q⁻¹ * r)) = x * y * z⁻¹ * (p * p⁻¹) * (q * q⁻¹) * (r * r⁻¹) := by
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [this]
  simp

theorem rU_tw (w : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ) (t : ∀ c, (H.obj c)ˣ) (s : ComposableArrows E 2) :
    rU (fun φ => tw w t φ) s = rU w s := by
  have key : ∀ {c₀ c₁ c₂ : E} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) (h : c₀ ⟶ c₂), h = f ≫ g →
      mu g (tw w t f) * tw w t g * (tw w t h)⁻¹ = mu g (w f) * w g * (w h)⁻¹ := by
    intro c₀ c₁ c₂ f g h e
    subst e
    unfold tw
    rw [map_mul, map_mul, map_inv, mu_comp]
    exact tw_units _ _ _ _ _ _
  exact key (s.map' 0 1) (s.map' 1 2) (s.map' 0 2) (s.map'_comp 0 1 2)

def wt (W : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ) (s : ComposableArrows E 1) : (H.obj (s.obj (Fin.last 1)))ˣ := W (s.map' 0 1)

def mt (s : ComposableArrows E 1) (x : (H.obj (s.obj 0))ˣ) : (H.obj (s.obj (Fin.last 1)))ˣ := mu (s.map' 0 1) x

theorem form_rep (hab : ∀ T x y, x ∈ a.S T → y ∈ a.S T → x * y ∈ b.S T) (W W' : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ)
    (hW : ∀ {c c' : E} (φ : c ⟶ c'), ((W φ : (H.obj c')ˣ) : H.obj c') - 1 ∈ a.S c')
    (hW' : ∀ {c c' : E} (φ : c ⟶ c'), ((W' φ : (H.obj c')ˣ) : H.obj c') - 1 ∈ a.S c')
    (τ : ∀ c, (H.obj c)ˣ) (hτ : ∀ {c c' : E} (φ : c ⟶ c'), W φ = W' φ * (τ c' * (mu φ (τ c))⁻¹))
    (u g : ∀ c, H.obj c) (h1 : ∀ c, (τ c : H.obj c) * u c - 1 ∈ a.S c) (h2 : ∀ c, g c + τ c ∈ a.S c)
    (hx : CH.d (sq a b) 1 (dl a b W hW - dl a b W' hW') = 0) :
    Rep a b (fun s : ComposableArrows E 1 => g (s.obj (Fin.last 1)) * (u (s.obj (Fin.last 1)) - mv s (u (s.obj 0))))
      ((CH.cx (sq a b)).cls _ hx) := by
  refine rep_of a b _ hx (c0 a b (fun c => (τ c : H.obj c) * u c - 1) h1) _ fun s => ?_
  have hc : Units.val (mt s (τ (s.obj 0))) * mv s (u (s.obj 0)) - 1 ∈ a.S (s.obj (Fin.last 1)) := by
    have := a.map_mem (s.map' 0 1) (h1 (s.obj 0))
    rw [map_sub, map_mul, map_one] at this
    exact this
  have hm : ((τ (s.obj (Fin.last 1)) : H.obj _) * u (s.obj (Fin.last 1)) - 1) -
      mv s ((τ (s.obj 0) : H.obj _) * u (s.obj 0) - 1) ∈ a.S (s.obj (Fin.last 1)) :=
    sub_mem (h1 _) (a.map_mem (s.map' 0 1) (h1 (s.obj 0)))
  have hWt : Units.val (wt W s) = Units.val (wt W' s) * (Units.val (τ (s.obj (Fin.last 1))) *
      ((mt s (τ (s.obj 0)))⁻¹ : (H.obj (s.obj (Fin.last 1)))ˣ).1) := congrArg Units.val (hτ (s.map' 0 1))
  have e := form_key (a.S (s.obj (Fin.last 1))) (b.S _) (hab _) (W := Units.val (wt W s))
    (W' := Units.val (wt W' s)) (Wi := ((wt W' s)⁻¹ : (H.obj (s.obj (Fin.last 1)))ˣ).1)
    (t := (τ (s.obj (Fin.last 1)) : H.obj _)) (ti := ((τ (s.obj (Fin.last 1)))⁻¹ : (H.obj _)ˣ).1)
    (c := Units.val (mt s (τ (s.obj 0)))) (m := ((mt s (τ (s.obj 0)))⁻¹ : (H.obj _)ˣ).1)
    (u := u (s.obj (Fin.last 1))) (e := mv s (u (s.obj 0))) (g := g (s.obj (Fin.last 1)))
    hWt (Units.mul_inv _) (Units.mul_inv _) (Units.mul_inv _) (hW _) (hW' _) (h1 _) hc (h2 _)
  have e2 : mv s ((τ (s.obj 0) : H.obj _) * u (s.obj 0) - 1) =
      Units.val (mt s (τ (s.obj 0))) * mv s (u (s.obj 0)) - 1 := by
    unfold mv
    rw [map_sub, map_mul, map_one]
    rfl
  have e3 := pderiv_comp1_pt_zero_eq_zero a b (fun c => (τ c : H.obj c) * u c - 1) h1 s hm
  have e4 : (dl a b W hW - dl a b W' hW' - CH.d (sq a b) 0 (c0 a b (fun c => (τ c : H.obj c) * u c - 1) h1)) s =
      dl a b W hW s - dl a b W' hW' s - CH.d (sq a b) 0 (c0 a b (fun c => (τ c : H.obj c) * u c - 1) h1) s := rfl
  rw [e4, e3]
  change Ideal.Quotient.mk (b.S (s.obj (Fin.last 1))) (Units.val (wt W s) - 1) - Ideal.Quotient.mk _ (Units.val (wt W' s) - 1) -
    Ideal.Quotient.mk _ (((τ (s.obj (Fin.last 1)) : H.obj _) * u (s.obj (Fin.last 1)) - 1) -
      mv s ((τ (s.obj 0) : H.obj _) * u (s.obj 0) - 1)) = _
  rw [← map_sub, ← map_sub, Ideal.Quotient.eq, e2]
  exact e.2

end Cat2

end GlobalTheory.CompanionTheory.OntoFirstChernCocycle
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPullbackSystemQuasicoherent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Shift

theorem exists_lift_pow_smul {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : N →ₗ[R] M) :
    ∃ k : ℕ, ∀ (n : ℕ) (y : N), f y ∈ J ^ (n + k) • (⊤ : Submodule R M) →
      ∃ i ∈ J ^ n • (⊤ : Submodule R N), f i = f y := by
  obtain ⟨k, hk⟩ := J.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨k, fun n y hy => ?_⟩
  have h1 : f y ∈ J ^ (n + k) • (⊤ : Submodule R M) ⊓ LinearMap.range f := ⟨hy, y, rfl⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h1
  have h2 : J ^ n • (J ^ k • (⊤ : Submodule R M) ⊓ LinearMap.range f) ≤
      (J ^ n • (⊤ : Submodule R N)).map f := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right
  obtain ⟨i, hi, hfi⟩ := h2 h1
  exact ⟨i, hi, hfi⟩

theorem mem_secs_adjKer {X Z : Scheme.{0}} (φ : Z ⟶ X) {E : X.Modules}
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (V : X.Opens) (x : Γ(E, V))
    (hx : (adjMap φ B).app V x = 0) : x ∈ secs (adjKer φ B) V := by
  obtain ⟨k, hk⟩ := kernel_ι_app_exact (adjMap φ B) V x hx
  refine ⟨(kernelSubobjectIso (adjMap φ B)).inv.app V k, ?_⟩
  rw [← hk, ← kernelSubobject_arrow' (adjMap φ B)]
  rfl

theorem local_shift {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X)
    (hφ : IsProper φ) (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) {E : X.Modules}
    (hE : IsCoherent E) (S : ℕ → Subobject E)
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (hB : (B : Z.Modules).IsQuasicoherent)
    (hBS : ∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e)
    (hK : (adjKer φ B : X.Modules).IsQuasicoherent)
    (V : X.Opens) (hV : IsAffineOpen V) :
    ∃ c : ℕ, ∀ e, secs (S (e + c)) V ⊆ secs (adjKer φ B ⊔ powSub I E (e + 1)) V := by
  haveI := hE.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow (isCoherent_pullback φ hE)
  have hP := GlobalTheory.T.proper_pushforward_coherent φ hφ hG
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.pushforward_ideal_power_shift I φ hφ hc hG V hV
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI := hP.2 V hV
  let f : Γ(E, V) →ₗ[Γ(X, V)] Γ((Scheme.Modules.pushforward φ).obj (cokernel B.arrow), V) :=
    { toFun := (adjMap φ B).app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  let J : Ideal Γ(X, V) := Ideal.map (toFunctions (A := A) V) I
  have hJ : ∀ m, Ideal.map (toFunctions (A := A) V) (I ^ m) = J ^ m := fun m => Ideal.map_pow _ _ _
  obtain ⟨c₂, hc₂⟩ := exists_lift_pow_smul J f
  refine ⟨c₂ + c₁, fun e x hx => ?_⟩
  have h1 := GlobalTheory.T.cokernel_section_ideal_power I φ S B (e + (c₂ + c₁)) (hBS _) V x hx
  rw [show e + (c₂ + c₁) + 1 = (e + 1 + c₂) + c₁ by omega] at h1
  have h2 := hc₁ (e + 1 + c₂) _ h1
  rw [hJ] at h2
  obtain ⟨i, hi, hfi⟩ := hc₂ (e + 1) x h2
  have hker : x - i ∈ secs (adjKer φ B) V :=
    mem_secs_adjKer φ B V _ (by
      change f (x - i) = 0
      rw [map_sub, hfi, sub_self])
  have hpow : i ∈ secs (powSub I E (e + 1)) V := by
    rw [GlobalTheory.T.ideal_power_subobject_sections I E hE.1 (e + 1) V hV, hJ]
    exact hi
  have hsup := (GlobalTheory.T.quasicoherent_sup_sections hE.1 (adjKer φ B) (powSub I E (e + 1)) hK
    ((closedSys_pow I E).qcoh e)).2 V hV
  rw [hsup]
  exact ⟨x - i, hker, i, hpow, by abel⟩

theorem shift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] [CompactSpace X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)), (B : Z.Modules).IsQuasicoherent → (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∃ c : ℕ, ∀ e, S (e + c) ≤ adjKer φ B ⊔ powSub I E (e + 1) := by
  intro A _ _ I X Z _ _ _ _ φ hφ hc E hE S hS B hB hBS
  haveI := hE.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow (isCoherent_pullback φ hE)
  have hP := GlobalTheory.T.proper_pushforward_coherent φ hφ hG
  haveI := hP.1
  have hK : (adjKer φ B : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubobjectIso (adjMap φ B)).symm (isQuasicoherent_kernel _)
  have hloc : ∀ V : X.affineOpens, ∃ c : ℕ,
      ∀ e, secs (S (e + c)) (V : X.Opens) ⊆ secs (adjKer φ B ⊔ powSub I E (e + 1)) (V : X.Opens) :=
    fun V => local_shift I φ hφ hc hE S B hB hBS hK V V.2
  choose c hc' using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hx, -⟩ :=
        exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩)
  have anti : Antitone S :=
    antitone_nat_of_succ_le fun n => le_of_le_of_eq le_sup_left (hS.succ n).symm
  refine ⟨t.sup c, fun e => ?_⟩
  have hsupq := (GlobalTheory.T.quasicoherent_sup_sections hE.1 (adjKer φ B) (powSub I E (e + 1)) hK
    ((closedSys_pow I E).qcoh e)).1
  refine GlobalTheory.T.subobject_le_of_affine_cover (S (e + t.sup c)) _ (hS.qcoh _) hsupq (fun i : t => (i.1.1 : X.Opens))
    (fun i => i.1.2) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hxU⟩
  · intro i
    refine subset_trans ?_ (hc' i.1 e)
    exact (_root_.GlobalTheory.CompanionTheory.GE.le_iff_secs_subset _ _).1 (anti (Nat.add_le_add_left (Finset.le_sup i.2) e)) i.1

end GlobalTheory.CompanionTheory.GE.Shift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotentVariant
section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeSub

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_iterate_eq_zero_of_subquot {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (π : Representation ℂ (GL ι F) V)
    (ρ : Representation ℂ (GL ι F) U) (hρ : IsSmooth ρ) (hfl : HasFiniteLength ρ)
    (hkill : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ →
      τ.IsIrreducible → IsSubquotient τ ρ → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0)
    (hns : ¬ IsSubquotient π ρ) (S : Subrepresentation ρ) :
    ∃ r : ℕ, ∀ u ∈ S.toSubmodule, u ∈ fixed ρ K → (hk ρ K e)^[r] u = 0 := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hfl
  induction S using WellFoundedLT.induction with
  | ind S ih =>
    by_cases hS : S = ⊥
    · subst hS
      exact ⟨0, fun u hu _ => hu⟩
    obtain ⟨T, hT, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {T | T < S}
      ⟨⊥, bot_lt_iff_ne_bot.2 hS⟩
    have hcov : T ⋖ S := ⟨hT, fun c h1 h2 => hmax c h2 h1⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hsq : IsSubquotient (subQuot S T) ρ := ⟨S, p, Submodule.mkQ_surjective _⟩
    have hne : IsEmpty ((subQuot S T).Equiv π) := ⟨fun φ => hns
      ((IsSubquotient.trans (IsSubquotient.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) hsq))⟩
    obtain ⟨r, hr⟩ := ih T hT
    refine ⟨r + 1, fun u huS hufix => ?_⟩
    have hfixS : (Submodule.mkQ _ (⟨u, huS⟩ : S.toSubmodule) :
        S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) ∈ fixed (subQuot S T) K := by
      intro h
      have h1 : ρ (h : GL ι F) u = u := by simpa using hufix h
      have h2 : S.toRepresentation (h : GL ι F) ⟨u, huS⟩ = ⟨u, huS⟩ := Subtype.ext h1
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      exact congrArg (Submodule.mkQ _) h2
    have h0 := hkill _ (subQuot S T) (hsq.isSmooth hρ) (isIrreducible_subQuot hcov) hsq hne _ hfixS
    have h1 : (hk S.toRepresentation K e ⟨u, huS⟩ : S.toSubmodule).1 = hk ρ K e u :=
      hk_map S.toRepresentation ρ S.toSubmodule.subtype (fun _ _ => rfl) hE ⟨u, huS⟩
    have h2 := hk_map S.toRepresentation (subQuot S T) (Submodule.mkQ _) (fun _ _ => rfl) hE ⟨u, huS⟩
    rw [h0] at h2
    have h3 : hk ρ K e u ∈ T.toSubmodule := by
      rw [← h1]
      exact (Submodule.Quotient.mk_eq_zero (T.toSubmodule.comap S.toSubmodule.subtype)).1 h2
    rw [Function.iterate_succ_apply]
    exact hr _ h3 (GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e hE U ρ u hufix).1

end GlobalTheory.CompanionTheory.HeckeSub
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuReductionCompat
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrysMid

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

noncomputable def trueRed (M : Model l K) (n : ℕ) :
    Mor (B.Lc (B.schFn M.p) (okToOC l K) true (n + 1)) (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).red (Nat.le_succ n)) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true (n + 1)) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).red (Nat.le_succ n)) rfl (B.dd_red true _ (Nat.le_succ n))
      (B.basePt _ _ (B.red_κb (okToOC l K) true (Nat.le_succ n))) fun _ _ _ => rfl

noncomputable def midRed (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n : ℕ) :
    Mor (Mid.Lm r M (n + 1)) (Mid.Lm r M n) ((base l).red (Nat.le_succ n)) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true (n + 1)) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).red (Nat.le_succ n)) rfl (B.dd_red true _ (Nat.le_succ n))
      (B.basePt _ _ (red_κm r (Nat.le_succ n))) fun _ _ _ => rfl

theorem ptIn_val (F : B.Fn (OK l K)) {r : CrystallineSemistableComparison.Res l K} {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (F.ptK (B.κb (okToOC l K) true n)).obj B₀) (h : (l : B₀) = 0) :
    ((Mid.ptIn F n hT).app B₀ y).1.2 = F.Pt.map (CommRingCat.ofHom (Mid.frbN h N)) y.1.2 := rfl

theorem base_val {O : Type} [CommRing O] (F : B.Fn O) {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {κ₁ : O →+* k₁} {κ₂ : O →+* k₂}
    (τ : k₁ →+* k₂) (h : τ.comp κ₁ = κ₂) (B₀ : CommRingCat.{0}) (y : (F.ptK κ₂).obj B₀) :
    ((B.basePt F τ h).app B₀ y).1.2 = y.1.2 := rfl

theorem ptIn_base (F : B.Fn (OK l K)) (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (F.ptK (B.κb (okToOC l K) true n)).obj B₀) :
    ((Mid.ptIn F (n + 1) hT).app B₀ ((B.basePt F _ (B.red_κb (okToOC l K) true (Nat.le_succ n))).app B₀ y)).1.2 =
      ((B.basePt F _ (red_κm r (Nat.le_succ n))).app B₀ ((Mid.ptIn F n hT).app B₀ y)).1.2 := by
  have h : (l : B₀) = 0 := Mid.l_zero y.1.1
  rw [ptIn_val F hT (n + 1) B₀ _ h, base_val, base_val, ptIn_val F hT n B₀ _ h]

theorem pt_sq (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (B.Lc (B.schFn M.p) (okToOC l K) true n).Pt.obj B₀) :
    ((Mid.mIn r M (n + 1) hT).pt.app B₀ ((trueRed M n).pt.app B₀ y)).1.2 =
      ((midRed r M n).pt.app B₀ ((Mid.mIn r M n hT).pt.app B₀ y)).1.2 :=
  ptIn_base (B.schFn M.p) r hT n B₀ y

theorem mid_square (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    (B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris n) (trueRed M n) (RingHom.id _) (B.red_cris _ (Nat.le_succ n))).pull j
      ((B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris (n + 1)) (Mid.mIn r M (n + 1) hT) (RingHom.id _) (Wc.idc _)).pull j t) =
    (B.omMor (c := (base l).cris n) (c' := (base l).cris n) (Mid.mIn r M n hT) (RingHom.id _) (Wc.idc _)).pull j
      ((B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris n) (midRed r M n) (RingHom.id _) (B.red_cris _ (Nat.le_succ n))).pull j t) :=
  cr_square (F₁ := B.schFn M.p) (F₂ := B.schFn M.p) (F₃ := B.schFn M.p) (F₄ := B.schFn M.p)
    (b₁ := B.bs l true (n + 1)) (b₂ := B.bs l true (n + 1)) (b₃ := B.bs l true n) (b₄ := B.bs l true n)
    (h₁ := rfl) (h₂ := rfl) (h₃ := rfl) (h₄ := rfl)
    (κ₁ := Mid.κm r (n + 1)) (κ₂ := B.κb (okToOC l K) true (n + 1)) (κ₃ := Mid.κm r n) (κ₄ := B.κb (okToOC l K) true n)
    (Λ := Acris l) (c₁ := (base l).cris (n + 1)) (c₂ := (base l).cris (n + 1)) (c₃ := (base l).cris n)
    (c₄ := (base l).cris n) (τ := RingHom.id _)
    (Mid.mIn r M (n + 1) hT) (trueRed M n) (midRed r M n) (Mid.mIn r M n hT)
    (Wc.idc _) (B.red_cris _ (Nat.le_succ n)) (B.red_cris _ (Nat.le_succ n)) (Wc.idc _) (fun x => (Wc.idc ((base l).red (Nat.le_succ n)) x).symm)
    (pt_sq r hT M n) j t

theorem mu_redHc (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j (Mid.mu r M (n + 1) j hT t) = Mid.mu r M n j hT ((redT r M (Nat.le_succ n)).pull j t) :=
  mid_square r hT M n j t

end GlobalTheory.CompanionTheory.CrysMid
end

