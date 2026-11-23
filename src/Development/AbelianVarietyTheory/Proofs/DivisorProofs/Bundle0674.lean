module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Functor
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Charts.Obj.cAlg

namespace GlobalTheory.AnPer.TenFam

open GlobalTheory.CatCoh

variable {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀}
  {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) (hπ : IsNilpotent (RingHom.ker π))
  {I : Type} [Fintype I] {F : Fam I g Λ} (K : Charts F) (ν : K₀.K → K.K)
  (Ta : ∀ k, Hol (K.W (ν k)) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k)) (τV : Hol F.V →+* D)
  (hc : ∀ k f, Ta k (K.cst (ν k) f) = τV f ⊗ₜ[ℂ] 1)

def obj (T : K₀.Obj) : K.Obj where
  k := ν T.k
  C := T.ten D
  alg := ((algebraMap D (T.ten D)).comp τV).toAlgebra
  J := T.tenJ π
  nil := T.tenJ_nil π hπ
  ρ := ((Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc).comp (Ta T.k)).toRingHom
  ρ_cst f := by
    change Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc (Ta T.k (K.cst (ν T.k) f)) = τV f ⊗ₜ[ℂ] (1 : T.C)
    rw [hc, Algebra.TensorProduct.map_tmul, map_one]
    rfl

variable (hν : ∀ l k' k, K₀.le l k' k → K.le l (ν k') (ν k))
  (hd : ∀ k a h, Ta k (dw (W := K.W (ν k)) a h) =
    LinearMap.lTensor D (dw (W := K₀.W k) a).toLinearMap (Ta k h))
  (hcl : ∀ l k' k (h₀ : K₀.le l k' k), Close ((RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k'))) ((Ta k').toRingHom.comp (Charts.sh (hν l k' k h₀))) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k')) (K₀.maps h₀))).comp (Ta k)).toRingHom))


include hd hcl in
theorem close {T T' : K₀.Obj} (f : T ⟶ T') :
    Close (T'.tenJ π) ((obj π hπ K ν Ta τV hc T').ρ.comp (Charts.sh (hν _ _ _ (Charts.Hom.le f))))
      ((Charts.Hom.ten D f : T.ten D →+* T'.ten D).comp (obj π hπ K ν Ta τV hc T).ρ) := by
  have h1 := (hcl _ _ _ (Charts.Hom.le f)).map (J' := T'.tenJ π)
    (Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc).toRingHom (fun c hc' ↦ by
      have : (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W T'.k)) ≤
          (T'.tenJ π).comap (Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc).toRingHom :=
        Ideal.map_le_iff_le_comap.2 fun d hd' ↦ by
          change T'.red π (d ⊗ₜ T'.ρc 1) ∈ T'.J
          rw [Charts.Obj.red_tmul, (RingHom.mem_ker).1 hd', map_zero, zero_mul]
          exact T'.J.zero_mem
      exact this hc')
  have h2 := GlobalTheory.AnPer.Close.tensor_comp (Ta T.k) (hd T.k) T'.J (T'.tenJ π) (fun c hc' ↦ by
      change T'.red π (1 ⊗ₜ c) ∈ T'.J
      rw [Charts.Obj.red_tmul]
      exact T'.J.mul_mem_left _ hc')
    (T'.ρc.comp (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k)) (K₀.maps (Charts.Hom.le f))))
    ((Charts.Hom.φc f).comp T.ρc) f.close
  have e1 : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc
      (Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k))
        (K₀.maps (Charts.Hom.le f))) x) = Algebra.TensorProduct.map (AlgHom.id ℂ D)
        (T'.ρc.comp (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k))
        (K₀.maps (Charts.Hom.le f)))) x := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul d c => rfl
  have e2 : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), Algebra.TensorProduct.map (AlgHom.id ℂ D) ((Charts.Hom.φc f).comp T.ρc) x =
      Charts.Hom.ten D f (Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc x) := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul d c => rfl
  have tr : ∀ {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C} {a b b' c c' : Hol W →+* C},
      Close J a b → Close J b' c → (∀ h, b h = b' h) → (∀ h, c h = c' h) → Close J a c' := by
    intro W C _ J a b b' c c' p q e e'
    obtain rfl : b = b' := RingHom.ext e
    obtain rfl : c = c' := RingHom.ext e'
    exact Relation.ReflTransGen.trans p q
  exact tr h1 h2 (fun h ↦ e1 (Ta T.k h)) (fun h ↦ e2 (Ta T.k h))

def functor : K₀.Obj ⥤ K.Obj where
  obj := obj π hπ K ν Ta τV hc
  map {T T'} f :=
    { φ := { (Charts.Hom.ten D f : T.ten D →+* T'.ten D) with commutes' := fun d ↦ (Charts.Hom.ten D f).commutes (τV d) }
      deg := f.deg
      le := hν _ _ _ (Charts.Hom.le f)
      mem := fun _ h ↦ Charts.Hom.ten_mem π f h
      close := close π hπ K ν Ta τV hc hν hd hcl f }
  map_id T := Charts.hom_ext (fun b ↦ mp_id (K₀.Ten D) T b) rfl
  map_comp f f' := Charts.hom_ext (fun b ↦ mp_comp (K₀.Ten D) f f' b) rfl

def coef : CoefMap τV K.Oc (K₀.Ten D) where
  G := functor π hπ K ν Ta τV hc hν hd hcl
  α T := RingHom.id (T.ten D)
  naturality _ _ := rfl
  smul T b c := (Algebra.smul_def (A := T.ten D) (τV b) c).symm

theorem main : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀) (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) {D₀ : Type} [CommRing D₀] {π₀ : D₀ →+* ℂ} (κ : DividedPowers (RingHom.ker π₀)) {s' : X₀ ⟶ Sp D₀} (hs : s' = s₀ ≫ spMap π₀) (io : D₀ →+* D) (hio : ∀ d, π (io d) = π₀ d) (hπ : IsNilpotent (RingHom.ker π)) {I : Type} [Fintype I] {F : Fam I g Λ} (K : Charts F) {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (r : Real K s σ) (ν : K₀.K → K.K) (hν : ∀ l k' k, K₀.le l k' k → K.le l (ν k') (ν k)) (Ta : ∀ k, Hol (K.W (ν k)) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k)) (τV : Hol F.V →+* D), (∀ k f, Ta k (K.cst (ν k) f) = τV f ⊗ₜ[ℂ] 1) → (∀ k a h, Ta k (dw (W := K.W (ν k)) a h) =
    LinearMap.lTensor D (dw (W := K₀.W k) a).toLinearMap (Ta k h)) → (∀ l k' k (h₀ : K₀.le l k' k), Close ((RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k'))) ((Ta k').toRingHom.comp (Charts.sh (hν l k' k h₀))) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k')) (K₀.maps h₀))).comp (Ta k)).toRingHom)) → ∀ (φ₀ : X₀ ⟶ X), (∀ k, spMap ((Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol (K₀.W k))).comp π) (AlgHom.id ℂ (Hol (K₀.W k))) (fun _ _ ↦ Commute.all _ _)).comp (Ta k)).toRingHom ≫ r.x (ν k) = r₀.x k ≫ φ₀) → ∀ (j : B →+* D₀) (n : IsMor (dp0 B) s κ s' j φ₀), (∀ b, io (j b) = τV (σ b)) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V) (q : Λ →+ D), (∀ l, q l = τV (per l)) → r.coef.pull1 c = K.perCl per → (r₀.tenCoef π hσ κ hs io hio hπ).pull1 (n.pull1 c) = GlobalTheory.CatCoh.H1.mk _ (K₀.tenZ q) := by
  intro I₀ _ g Λ _ F₀ K₀ D _ _ π X₀ s₀ σ₀ r₀ hσ D₀ _ π₀ κ s' hs io hio hπ I _ F K B _ X s σ r ν hν Ta τV hc hd hcl φ₀ hpt
    j n hj c per q hq hper
  let β := coef π hπ K ν Ta τV hc hν hd hcl
  let θ : (r.coef.comp β).G ⟶ (n.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)).G :=
    { app := fun T ↦
        { φ := { RingHom.id (T.ten D) with commutes' := fun b ↦ congrArg (algebraMap D (T.ten D)) (hj b).symm }
          φ₀ := Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl
          comm := fun _ ↦ rfl
          dp := letI := T.tenRat (D := D); isDPMorphism_of_rat _ (T.tenδ π) (RingHom.id (T.ten D)) fun _ h ↦ h
          pt := by
            have e : (Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl).comp
                ((Ideal.Quotient.mk (T.tenJ π)).comp (obj π hπ K ν Ta τV hc T).ρ) =
                ((Ideal.Quotient.mk T.J).comp T.ρ).comp ((Algebra.TensorProduct.lift
                  ((Algebra.ofId ℂ (Hol (K₀.W T.k))).comp π) (AlgHom.id ℂ (Hol (K₀.W T.k)))
                  (fun _ _ ↦ Commute.all _ _)).comp (Ta T.k)).toRingHom := by
              have e' : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), T.red π (Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc x) =
                  T.ρc (Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol (K₀.W T.k))).comp π)
                    (AlgHom.id ℂ (Hol (K₀.W T.k))) (fun _ _ ↦ Commute.all _ _) x) := fun x ↦ by
                induction x using TensorProduct.induction_on with
                | zero => simp only [map_zero]
                | add x y hx hy => simp only [map_add (f := _), hx, hy]
                | tmul d c =>
                  rw [Algebra.TensorProduct.lift_tmul, map_mul]
                  exact congrArg (· * T.ρc c) (T.ρc.commutes (π d)).symm
              exact RingHom.ext fun h ↦ congrArg (Ideal.Quotient.mk T.J) (e' (Ta T.k h))
            change spMap (Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl) ≫
              spMap ((Ideal.Quotient.mk (T.tenJ π)).comp (obj π hπ K ν Ta τV hc T).ρ) ≫ r.x (ν T.k) =
              (spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ r₀.x T.k) ≫ φ₀
            rw [Category.assoc, ← hpt]
            exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r.x (ν T.k)) ((Cris.spMap_comp _ _).symm.trans
              ((congrArg spMap e).trans (Cris.spMap_comp _ _)))).trans (Category.assoc _ _ _)) }
      naturality := fun _ _ _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  have h1 := (r.coef.comp β).pullCohomologyOne_eq_of_natTrans (n.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)) θ (fun _ _ ↦ rfl) c
  rw [CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_comp, hper] at h1
  refine h1.symm.trans (congrArg (GlobalTheory.CatCoh.H1.mk _) (Subtype.ext ?_))
  funext T T' f
  change algebraMap D (T'.ten D) (τV (per f.deg)) = algebraMap D (T'.ten D) (q f.deg)
  rw [hq]

end GlobalTheory.AnPer.TenFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharacterCoxeterTorusInvEqAtInverse
section
open Polynomial

noncomputable section

namespace GlobalTheory.CuspInv

open GlobalTheory.IndefiniteRowSideFullHecke

def mirrorEquiv (k : Type) [Field k] : k[X] ≃* k[X] where
  toFun := mirror
  invFun := mirror
  left_inv := fun f => mirror_mirror f
  right_inv := fun f => mirror_mirror f
  map_mul' := fun f g => mirror_mul_of_domain f g

theorem powIrr_of_inv {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι] (h h' : Matrix ι ι k)
    (hh : h * h' = 1) (H : ∃ (φ : k[X]) (n : ℕ), Irreducible φ ∧ h.charpoly = φ ^ n) :
    ∃ (φ : k[X]) (n : ℕ), Irreducible φ ∧ h'.charpoly = φ ^ n := by
  classical
  obtain ⟨φ, n, hφ, hn⟩ := H
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 (Matrix.isUnit_det_of_right_inverse hh)
  have hinv : h' = h⁻¹ := (Matrix.inv_eq_right_inv hh).symm
  have hdet : h.det ≠ 0 := (Matrix.isUnit_det_of_right_inverse hh).ne_zero
  have h0 : h.charpoly.coeff 0 ≠ 0 := by
    intro h0
    exact hdet (by rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero])
  have hm : h.charpoly.mirror = h.charpolyRev := by
    rw [mirror, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (p := h.charpoly) h0, pow_zero, mul_one,
      Matrix.reverse_charpoly]
  have hψ : Irreducible (mirrorEquiv k φ) := (MulEquiv.irreducible_iff (mirrorEquiv k)).2 hφ
  have h1 : h.charpolyRev = (mirrorEquiv k φ) ^ n := by
    rw [← map_pow, ← hn, ← hm]; rfl
  have hass : Associated h'.charpoly ((normalize (mirrorEquiv k φ)) ^ n) := by
    refine Associated.trans ?_ ((associated_normalize _).pow_pow)
    rw [hinv, Matrix.charpoly_inv h hu, h1]
    refine associated_unit_mul_left _ _ ?_
    refine IsUnit.mul (IsUnit.pow _ isUnit_one.neg) ?_
    rw [isUnit_C, Ring.inverse_eq_inv', isUnit_iff_ne_zero]
    exact inv_ne_zero hdet
  refine ⟨normalize (mirrorEquiv k φ), n, (associated_normalize _).irreducible hψ, ?_⟩
  exact eq_of_monic_of_associated h'.charpoly_monic ((monic_normalize hψ.ne_zero).pow n) hass

theorem eigenspace_le {L V : Type} [Field L] [AddCommGroup V] [Module L V] (f g : Module.End L V)
    (hfg : g * f = 1) (z : L) : f.eigenspace z ≤ g.eigenspace z⁻¹ := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h1 : g (f v) = v := by rw [← Module.End.mul_apply, hfg]; rfl
  rw [hv, map_smul] at h1
  by_cases hz : z = 0
  · subst hz
    rw [zero_smul] at h1
    rw [← h1]; simp
  · conv_rhs => rw [← h1]
    rw [smul_smul, inv_mul_cancel₀ hz, one_smul]

theorem eigenspace_inv {L V : Type} [Field L] [AddCommGroup V] [Module L V] (f g : Module.End L V)
    (hfg : f * g = 1) (hgf : g * f = 1) (z : L) : g.eigenspace z⁻¹ = f.eigenspace z := by
  refine le_antisymm ?_ (eigenspace_le f g hgf z)
  simpa using eigenspace_le g f hfg z⁻¹

theorem mem_aroots_iff {k L ι : Type} [Field k] [Field L] [Algebra k L] [Fintype ι] [DecidableEq ι]
    (h : Matrix ι ι k) (z : L) :
    z ∈ h.charpoly.aroots L ↔
      Module.End.eigenspace (Matrix.toLin' (h.map (algebraMap k L))) z ≠ ⊥ := by
  rw [← Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Matrix.charpoly_toLin', Matrix.charpoly_map, mem_aroots, IsRoot, eval_map_algebraMap]
  simp [h.charpoly_monic.ne_zero]

theorem torVal_inv {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {d : ℕ} (θ : LevelCuspCharacters.Tor p d →* Kˣ)
    (z : LevelCuspCharacters.Fbar p) : LevelCuspCharacters.torVal θ⁻¹ z = LevelCuspCharacters.torVal θ z⁻¹ := by
  have hinj : Function.Injective
      (fun u : LevelCuspCharacters.Tor p d => ((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p)) :=
    fun a b hab => Subtype.ext (Units.ext hab)
  unfold LevelCuspCharacters.torVal
  by_cases hz : ∃ u : LevelCuspCharacters.Tor p d, ((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p) = z
  · obtain ⟨u, rfl⟩ := hz
    have h2 : (((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p))⁻¹ =
        (((u⁻¹ : LevelCuspCharacters.Tor p d) : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p) := by simp
    rw [h2, hinj.extend_apply, hinj.extend_apply]
    simp
  · rw [Function.extend_apply' _ _ _ hz, Function.extend_apply']
    · rfl
    · rintro ⟨u, hu⟩
      exact hz ⟨u⁻¹, by simp [hu]⟩

theorem cuspChar_inv : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (ι : Type) [Fintype ι]
    [DecidableEq ι] (θ : LevelCuspCharacters.Tor p (Fintype.card ι) →* Kˣ) (h h' : Matrix ι ι (ZMod p)),
    h * h' = 1 → LevelCuspCharacters.cuspChar θ⁻¹ h = LevelCuspCharacters.cuspChar θ h' := by
  intro p _ K _ ι _ _ θ h h' hh
  classical
  have hh' : h' * h = 1 := mul_eq_one_comm.1 hh
  have key : ∀ (a b : Matrix ι ι (ZMod p)), a * b = 1 →
      Matrix.toLin' (a.map (algebraMap (ZMod p) (LevelCuspCharacters.Fbar p))) *
        Matrix.toLin' (b.map (algebraMap (ZMod p) (LevelCuspCharacters.Fbar p))) = 1 := by
    intro a b hab
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hab,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
    rfl
  have heig := eigenspace_inv _ _ (key h h' hh) (key h' h hh')
  have hmem : ∀ z : LevelCuspCharacters.Fbar p, z ∈ (h.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset ↔
      z⁻¹ ∈ (h'.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset := by
    intro z
    rw [Multiset.mem_toFinset, Multiset.mem_toFinset, mem_aroots_iff, mem_aroots_iff, heig]
  have hcard : (h.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset.card =
      (h'.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset.card :=
    Finset.card_bijective _ inv_involutive.bijective hmem
  unfold LevelCuspCharacters.cuspChar
  by_cases H : ∃ (φ : (ZMod p)[X]) (n : ℕ), Irreducible φ ∧ h.charpoly = φ ^ n
  · rw [if_pos H, if_pos (powIrr_of_inv h h' hh H)]
    congr 1
    refine Finset.sum_bijective _ inv_involutive.bijective (by convert hmem) ?_
    intro z _
    rw [torVal_inv, heig]
    congr 2
    funext i
    congr 3
  · rw [if_neg H, if_neg (fun H' => H (powIrr_of_inv h' h hh' H'))]

end GlobalTheory.CuspInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepBasicOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixTransport

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_pull {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X)
    (G' : Z ⟶ Y') (h : G ≫ F = G' ≫ F') : LBIso ((L.pull F).pull G) ((L.pull F').pull G') :=
  LBIso.chartPull
    (chartPullLinComb L F (fun _ : PUnit => G) (fun _ => G ≫ F) (fun _ => 1) (𝟙 Z)
      fun _ => (Category.id_comp _).symm)
    (chartPullLinComb L F' (fun _ : PUnit => G') (fun _ => G ≫ F) (fun _ => 1) (𝟙 Z)
      fun _ => by rw [Category.id_comp, h])
    (lbIso_self (pull_isLB hL (G ≫ F)))

theorem lbIso_pull {X Y : Scheme.{0}} {L M : LB X} (H : LBIso L M) (h : Y ⟶ X) : LBIso (L.pull h) (M.pull h) :=
  LBIso.chartPull (chartPullPull L h h rfl) (chartPullPull M h h rfl) H

theorem lbIso_congr {X : Scheme.{0}} {P P' Q Q' : LB X} (hP : P.IsLB) (hP' : P'.IsLB) (hQ : Q.IsLB) (hQ' : Q'.IsLB)
    (e₁ : LBIso P' P) (H : LBIso P Q) (e₂ : LBIso Q Q') : LBIso P' Q' :=
  LBIso.trans hP' hQ hQ' (LBIso.trans hP' hP hQ e₁ H) e₂

section Transport

variable {S S₁ S₂ : Scheme.{0}} (e : S₁ ≅ S₂) {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
  (hL : L.IsLB) (hM : M.IsLB) {Af Bf : Over S₂} [GrpObj Af] [GrpObj Bf] (φA : Af.left ⟶ A.left)
  (φB : Bf.left ⟶ B.left)

def transport (R : HomFixRep Af Bf (L.pull φA) (M.pull φB)) :
    HomFixRep ((Over.pullback e.hom).obj Af) ((Over.pullback e.hom).obj Bf)
      (L.pull (pullback.fst Af.hom e.hom ≫ φA)) (M.pull (pullback.fst Bf.hom e.hom ≫ φB)) where
  H := R.H
  π := R.π ≫ e.inv
  AH := R.AH
  BH := R.BH
  φA := pullback.lift R.φA (R.AH.hom ≫ R.π ≫ e.inv) (by simp [R.pbA.1.w])
  φB := pullback.lift R.φB (R.BH.hom ≫ R.π ≫ e.inv) (by simp [R.pbB.1.w])
  pbA := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e.hom (R.π ≫ e.inv) (R.pbA.congr (by simp) rfl)
  pbB := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e.hom (R.π ≫ e.inv) (R.pbB.congr (by simp) rfl)
  Φ := R.Φ
  hom := R.hom
  iso := lbIso_congr (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)
    (pull_isLB (pull_isLB (pull_isLB hM _) _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
    (lbIso_pull_pull hL _ _ _ _ (by erw [pullback.lift_fst_assoc])) R.iso
    (lbIso_pull (lbIso_pull_pull hM _ _ _ _ (by erw [pullback.lift_fst_assoc])) _)
  rep := by
    intro T t A' B' _ _ φA' φB' Φ' hA hB hΦ hI
    have hA₂ := hA.comp (isGrpPullback_pullback Af e.hom)
    have hB₂ := hB.comp (isGrpPullback_pullback Bf e.hom)
    obtain ⟨h, ⟨hπ, ψA, ψB, pA, pB, eA, eB, eΦ⟩, hu⟩ := R.rep T (t ≫ e.hom) A' B'
      (φA' ≫ pullback.fst Af.hom e.hom) (φB' ≫ pullback.fst Bf.hom e.hom) Φ' hA₂ hB₂ hΦ
      (lbIso_congr (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)
        (pull_isLB (pull_isLB (pull_isLB hM _) _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
        (lbIso_pull_pull hL φA (φA' ≫ pullback.fst Af.hom e.hom) (pullback.fst Af.hom e.hom ≫ φA) φA' (by simp)) hI
        (lbIso_pull (lbIso_pull_pull hM (pullback.fst Bf.hom e.hom ≫ φB) φB' φB (φB' ≫ pullback.fst Bf.hom e.hom)
          (by simp)) Φ'.left))
    refine ⟨h, ⟨?_, ψA, ψB, pA, pB, ?_, ?_, eΦ⟩, ?_⟩
    · rw [← Category.assoc, hπ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst]; exact eA
      · simp only [Category.assoc, pullback.lift_snd]
        rw [reassoc_of% pA.1.w, reassoc_of% hπ, Iso.hom_inv_id, Category.comp_id]
        exact hA.1.w.symm
    · apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst]; exact eB
      · simp only [Category.assoc, pullback.lift_snd]
        rw [reassoc_of% pB.1.w, reassoc_of% hπ, Iso.hom_inv_id, Category.comp_id]
        exact hB.1.w.symm
    · rintro h' ⟨hπ', ψA', ψB', pA', pB', eA', eB', eΦ'⟩
      refine hu h' ⟨by rw [← hπ']; simp, ψA', ψB', pA', pB', by rw [← eA', Category.assoc]; erw [pullback.lift_fst],
        by rw [← eB', Category.assoc]; erw [pullback.lift_fst], eΦ'⟩

end Transport

end GlobalTheory.HomFixTransport


open GlobalTheory.HomFixTransport in
theorem GlobalTheory.HomFixTransport.homFixRep_basicOpen : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (f : Rg), L.IsLB → M.IsLB → (∀ (Af Bf : Over (Sp (Localization.Away f))) [GrpObj Af] [GrpObj Bf] (φA : Af.left ⟶ A.left) (φB : Bf.left ⟶ B.left), IsGrpPullback Af A (spMap (algebraMap Rg (Localization.Away f))) φA → IsGrpPullback Bf B (spMap (algebraMap Rg (Localization.Away f))) φB → ∃ R : HomFixRep Af Bf (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∀ U : (Sp Rg).Opens, U = PrimeSpectrum.basicOpen f → ∃ (AU : Over U.toScheme) (_ : GrpObj AU) (BU : Over U.toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A U.ι φA ∧ IsGrpPullback BU B U.ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ A B _ _ L M f hL hM hyp U hU
  have hr : Set.range U.ι = Set.range (spMap (algebraMap Rg (Localization.Away f))) := by
    rw [Scheme.Opens.range_ι, hU]
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm
  haveI : IsOpenImmersion (spMap (algebraMap Rg (Localization.Away f))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Rg (Localization.Away f)))))
  let e := IsOpenImmersion.isoOfRangeEq U.ι (spMap (algebraMap Rg (Localization.Away f))) hr
  have he : e.hom ≫ spMap (algebraMap Rg (Localization.Away f)) = U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨R, h₁, h₂, h₃⟩ := hyp _ _ _ _ (isGrpPullback_pullback A (spMap (algebraMap Rg (Localization.Away f))))
    (isGrpPullback_pullback B (spMap (algebraMap Rg (Localization.Away f))))
  refine ⟨_, inferInstance, _, inferInstance, _, _,
    ((isGrpPullback_pullback _ e.hom).comp (isGrpPullback_pullback A _)).congr he rfl,
    ((isGrpPullback_pullback _ e.hom).comp (isGrpPullback_pullback B _)).congr he rfl,
    transport e hL hM _ _ R, ?_, ?_, ?_⟩
  · show QuasiCompact (R.π ≫ e.inv); infer_instance
  · show IsSeparated (R.π ≫ e.inv); infer_instance
  · show LocallyOfFiniteType (R.π ≫ e.inv); infer_instance
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepOfUniversal
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open Opposite

namespace GlobalTheory.EndLoc.HomFixGlue

theorem pullPull_mem {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X) (G' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (hc : G' ≫ F' = h ≫ G ≫ F) (J : PUnit → PUnit → M.ι) (y : Z')
    (hy : y ∈ ((M.pull F').pull G').U J) :
    h y ∈ ((M.pull F).pull G).U (fun _ => fun _ => J PUnit.unit PUnit.unit) := by
  have h1 := mem_pull.1 (mem_pull.1 hy)
  have e : F (G (h y)) = F' (G' y) := by
    have := congrArg (fun k => k y) hc
    simpa using this.symm
  exact mem_pull.2 (mem_pull.2 (by rw [e]; exact h1))

def chartPullPullPull {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X) (G' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (hc : G' ≫ F' = h ≫ G ≫ F) : ChartPull ((M.pull F').pull G') ((M.pull F).pull G) h where
  idx J := fun _ => fun _ => J PUnit.unit PUnit.unit
  le J y hy := pullPull_mem M F G F' G' h hc J y hy
  g y J J' hj hj' := by
    have a1 := gm_pull_g (M.pull F') G' (𝟙 _) y J J' hj hj'
    have a2 := gm_pull_g M F' (𝟙 _ ≫ G') y (J PUnit.unit) (J' PUnit.unit) (mem_pull.1 hj) (mem_pull.1 hj')
    have m1 := pullPull_mem M F G F' G' h hc J y hj
    have m2 := pullPull_mem M F G F' G' h hc J' y hj'
    have b1 := gm_pull_g (M.pull F) G h y _ _ m1 m2
    have b2 := gm_pull_g M F (h ≫ G) y (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
      (mem_pull.1 m1) (mem_pull.1 m2)
    rw [a1, a2, b1, b2]
    have e : (𝟙 _ ≫ G') ≫ F' = (h ≫ G) ≫ F := by simp [hc]
    rw [e]

section
variable {S : Scheme.{0}}

variable (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)

end

end GlobalTheory.EndLoc.HomFixGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNarrowRayClassLFunctionTopWideIndicatorIff
section
noncomputable section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.ZetaDenom

theorem isRayL_top_wideInd_iff : ∀ {F : Type} [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ),
    IsRayL (⊤ : Ideal (𝓞 F)) (wideInd C) Z ↔ IsClassZeta C Z := by
  intro F _ _ C Z
  refine and_congr_right fun _ => forall₂_congr fun s _ => ?_
  let g : IdealsIn C → {I : Ideal (𝓞 F) // CoprimeTo F ⊤ I} :=
    fun I => ⟨I.1.1, nonZeroDivisors.coe_ne_zero I.1, sup_top_eq _⟩
  have hg : Function.Injective g := fun I J h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : {I : Ideal (𝓞 F) // CoprimeTo F ⊤ I} => x.1) h))
  rw [← hg.hasSum_iff (f := fun I : {I : Ideal (𝓞 F) // CoprimeTo F ⊤ I} =>
    (wideInd C I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) fun I hI => by
      have : cls I.1 ≠ C := fun h => hI ⟨⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2.1⟩,
        by rw [← h, cls_of_ne_bot I.2.1]⟩, rfl⟩
      simp [wideInd, this]]
  refine iff_of_eq (congrArg (HasSum · (Z s)) (funext fun I => ?_))
  have h1 : cls (I.1 : Ideal (𝓞 F)) = C := by
    rw [cls_of_ne_bot (nonZeroDivisors.coe_ne_zero I.1)]
    exact I.2
  simp [g, wideInd, h1]

end GlobalTheory.ZetaDenom
end
end

