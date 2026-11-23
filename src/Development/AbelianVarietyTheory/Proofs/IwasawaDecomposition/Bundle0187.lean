module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceModelSum

open GlobalTheory.PlaceModel

theorem smul_tmul_one {F A E : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E]
    (t : F) (a : A) : (t • a) ⊗ₜ[F] (1 : E) = a ⊗ₜ[F] algebraMap F E t := by
  rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem trace_laws {R : Type} [CommRing R] {e c e' c' : R} (h1 : e * e = e) (c1 : c * c = c) (h2 : e * c = 0)
    (h1' : e' * e' = e') (c1' : c' * c' = c') (h2' : e' * c' = 0) :
    (e * e' + c * c') * (e * e' + c * c') = e * e' + c * c' ∧ (e + c) * (e * e' + c * c') = e * e' + c * c' ∧
      (e' + c') * (e * e' + c * c') = e * e' + c * c' ∧ (0 = e * e' + c * c' → e * e' = 0) ∧
      (e + c = e * e' + c * c' → e' + c' = e * e' + c * c' → e = e') :=
  ⟨by linear_combination (e' * e') * h1 + e * h1' + (c' * c') * c1 + c * c1' + (2 * e' * c') * h2,
    by linear_combination e' * h1 + c' * c1 + (e' + c') * h2,
    by linear_combination e * h1' + c * c1' + (e + c) * h2',
    fun ht => by linear_combination (-e) * ht - e' * h1 - c' * h2,
    fun b1 b2 => by
      linear_combination e * b1 - e' * b2 - h1 - h2 + h1' + h2' + e' * h1 + c' * h2 - e * h1' - c * h2'⟩

theorem eq_or_orth {A R : Type} [CommRing A] [CommRing R] (ι : A →+* R) (hinj : Function.Injective ι)
    {e c e' c' : R} {ε ε' t : A} (h1 : e * e = e) (c1 : c * c = c) (h2 : e * c = 0)
    (h1' : e' * e' = e') (c1' : c' * c' = c') (h2' : e' * c' = 0) (h3 : e + c = ι ε) (h3' : e' + c' = ι ε')
    (ht : ι t = e * e' + c * c') (p : t * t = t → ε * t = t → t = 0 ∨ t = ε)
    (p' : t * t = t → ε' * t = t → t = 0 ∨ t = ε') : e = e' ∨ e * e' = 0 := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := trace_laws h1 c1 h2 h1' c1' h2'
  rw [← ht] at k1 k2 k3 k4 k5
  rw [h3] at k2 k5
  rw [h3'] at k3 k5
  have tt : t * t = t := hinj (by rw [map_mul]; exact k1)
  have t1 : ε * t = t := hinj (by rw [map_mul]; exact k2)
  have t2 : ε' * t = t := hinj (by rw [map_mul]; exact k3)
  by_cases h0 : t = 0
  · exact Or.inr (k4 (by rw [h0, map_zero]))
  · exact Or.inl (k5 (by rw [← (p tt t1).resolve_left h0]) (by rw [← (p' tt t2).resolve_left h0]))

variable {D : D7}

theorem exists_add_conj (a : AE D) : ∃ t : AF D.host.F, algebraMap (AF D.host.F) (AE D) t = a + cA D a := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [RingHom.map_zero, RingHom.map_zero, add_zero]⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hs, ht]; ring⟩
  | tmul a x =>
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    obtain ⟨t, ht⟩ : ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add (f := _), hσ, add_comm]
    refine ⟨t • a, ?_⟩
    change (t • a) ⊗ₜ[D.host.F] (1 : D.host.E) = a ⊗ₜ[D.host.F] x + a ⊗ₜ[D.host.F] D.sp.cm.sig x
    rw [← TensorProduct.tmul_add, ← ht, smul_tmul_one]

theorem eq_zero_or_eq_of_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε t : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (ht : t * t = t) (hεt : ε * t = t) : t = 0 ∨ t = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have e1 : t.1 = 0 := by
    have : (0 : Ainf D.host.F) * t.1 = t.1 := congrArg Prod.fst hεt
    rw [← this, zero_mul]
  have e2 : α * t.2 = t.2 := congrArg Prod.snd hεt
  have e3 : t.2 * t.2 = t.2 := congrArg Prod.snd ht
  have e4 : ∀ w, w ≠ v → evalV D.host.F w t.2 = 0 := fun w hw => by rw [← e2, map_mul, h0 w hw, zero_mul]
  have e5 : evalV D.host.F v t.2 * (evalV D.host.F v t.2 - 1) = 0 := by
    rw [mul_sub, ← map_mul, e3, mul_one, sub_self]
  have ext : ∀ β : Af D.host.F, (∀ w, evalV D.host.F w t.2 = evalV D.host.F w β) → t = pairA D.host.F 0 β :=
    fun β h => Prod.ext e1 (RestrictedProduct.ext _ _ h)
  rcases mul_eq_zero.1 e5 with h | h
  · refine Or.inl (ext 0 fun w => ?_)
    rw [map_zero]
    by_cases hw : w = v
    · rw [hw, h]
    · exact e4 w hw
  · refine Or.inr (ext α fun w => ?_)
    by_cases hw : w = v
    · rw [hw, h1, sub_eq_zero.1 h]
    · rw [e4 w hw, h0 w hw]

theorem eq_or_mul_eq_zero {e e' : AE D} (he : IsSplitIdem D e) (he' : IsSplitIdem D e') : e = e' ∨ e * e' = 0 := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  obtain ⟨h1', h2', v', ε', hε', h3'⟩ := he'
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  have c1 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have c1' : cA D e' * cA D e' = cA D e' := by rw [← map_mul, h1']
  obtain ⟨t, ht⟩ := exists_add_conj (e * e')
  rw [RingHom.map_mul] at ht
  exact eq_or_orth _ hinj h1 c1 h2 h1' c1' h2' h3 h3' ht (eq_zero_or_eq_of_placeIdem hε)
    (eq_zero_or_eq_of_placeIdem hε')

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

def IsOrthSum (e : AE D) : Prop :=
  ∃ (ι : Type) (P : Finset ι) (es : ι → AE D), (∀ i ∈ P, IsSplitIdem D (es i)) ∧
    (∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0) ∧ e = ∑ i ∈ P, es i

theorem isOrthSum_of_isIdemSum {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    IsOrthSum e := by
  obtain ⟨⟨es, h1, h2⟩, -⟩ := h
  refine ⟨_, P, es, fun i hi => (h1 i hi).1, fun i hi j hj hij => ?_, h2⟩
  refine (eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h => hij ?_
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [(h1 i hi).2 x hx, (h1 j hj).2 x hx, h]

theorem IsOrthSum.conj {e : AE D} (h : IsOrthSum e) : IsOrthSum (cA D e) := by
  obtain ⟨ι, P, es, h1, h2, rfl⟩ := h
  exact ⟨ι, P, fun i => cA D (es i), fun i hi => isSplitIdem_cA (h1 i hi),
    fun i hi j hj hij => by rw [← map_mul, h2 i hi j hj hij, map_zero], map_sum _ _ _⟩

theorem mul_sum_orth {ι : Type} {P : Finset ι} {es : ι → AE D} (h1 : ∀ i ∈ P, IsSplitIdem D (es i))
    (h2 : ∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0) {i : ι} (hi : i ∈ P) : es i * ∑ j ∈ P, es j = es i := by
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem i hi (h2 i hi), (h1 i hi).1]

theorem IsOrthSum.idem {e : AE D} (h : IsOrthSum e) : e * e = e := by
  obtain ⟨ι, P, es, h1, h2, rfl⟩ := h
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi => mul_sum_orth h1 h2 hi

theorem infPart_split {e : AE D} (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨β, rfl, -⟩, h3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have : e = (e + cA D e) * e := by linear_combination -h1 - h2
  rw [this, h3, map_mul, h0, zero_mul]

theorem IsOrthSum.infPart_eq {e : AE D} (h : IsOrthSum e) : infPart D e = 0 := by
  obtain ⟨ι, P, es, h1, -, rfl⟩ := h
  exact Finset.sum_induction _ (fun y => infPart D y = 0)
    (fun x y hx hy => by rw [RingHom.map_add (f := _), hx, hy, add_zero]) (RingHom.map_zero _) fun i hi => infPart_split (h1 i hi)

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem idem_smul_latO {e : AE D} (he : e * e = e) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    e • u ∈ latO S T LS LT fun _ => True :=
  GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ e (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])) u hu

theorem idem_smul_half {e : AE D} (he : e * e = e) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    e • u ∈ (latO S T LS LT fun _ => True) ⊓ half S T e :=
  AddSubgroup.mem_inf.2 ⟨idem_smul_latO he hu, by rw [mem_half, smul_smul, he]⟩

theorem IsOrthSum.infPart_half {e : AE D} (h : IsOrthSum e) {u : WO S T} (hu : u ∈ half S T e) :
    u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, ← (isHalf_iff S T).2 hu i j, map_mul, h.infPart_eq, zero_mul]
  rfl

theorem IsOrthSum.heisO_eq {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} (h : IsOrthSum e) (hec : cA D e * e = 0)
    {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) f) (u : WO S T)
    (hu : u ∈ (latO S T LS LT fun _ => True) ⊓ half S T e) : heisO ψ S T u f = f := by
  obtain ⟨ι, P, es, h1, h2, he⟩ := h
  have e1 : u = ∑ i ∈ P, es i • u := by rw [← Finset.sum_smul, ← he, (mem_half S T).1 hu.2]
  have key : (∑ i ∈ P, es i • u) ∈ half S T e ∧ heisL S T ψ (∑ i ∈ P, es i • u) f = f := by
    refine Finset.sum_induction _ (fun y => y ∈ half S T e ∧ heisL S T ψ y f = f) (fun x y hx hy => ?_) ?_
      fun i hi => ?_
    · exact ⟨add_mem hx.1 hy.1, by rw [← heisL_half S T ψ hec x hx.1 y hy.1, hy.2, hx.2]⟩
    · exact ⟨zero_mem _, GlobalTheory.LatVac.heisO_zero ψ f⟩
    · have := idem_smul_half (h1 i hi).1 hu.1
      refine ⟨?_, hf.2 _ (h1 i hi) _ this.1 ((isHalf_iff S T).2 this.2)⟩
      rw [mem_half, smul_smul, mul_comm, he, mul_sum_orth h1 h2 hi]
  rw [← e1] at key
  exact key.2

theorem IsOrthSum.mem_of_dual {ψ : AddChar (AF D.host.F) ℂ}
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ (latO S T LS LT fun _ => True) ↔
      ∀ u' ∈ (latO S T LS LT fun _ => True), ψ (symplO S T u u') = 1))
    {a : AE D} (ha : IsOrthSum a) (x : WO S T) (hx : x ∈ half S T a)
    (h : ∀ y ∈ (latO S T LS LT fun _ => True) ⊓ half S T (cA D a), ψ (symplO S T x y) = 1) :
    x ∈ (latO S T LS LT fun _ => True) ⊓ half S T a :=
  AddSubgroup.mem_inf.2 ⟨(hdual x (ha.infPart_half hx)).2 fun u hu => by
    have := h _ (idem_smul_half ha.conj.idem hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this, hx⟩

theorem IsOrthSum.exists_model {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} (he : IsOrthSum e) (hec : e * cA D e = 0)
    {f₀ : WO S T → ℂ} (hvac : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  refine exists_placeModel ψ hec _ (fun u hu y hy => (hdual u (he.infPart_half hu.2)).1 hu.1 y hy.1)
    (he.mem_of_dual hdual) (fun y hy h => ?_) (fun k hk => ?_) one_ne_zero f₀
    (he.heisO_eq (by rw [mul_comm, hec]) hvac) (he.conj.heisO_eq (by rw [cA_cA, hec]) hvac)
  · refine he.conj.mem_of_dual hdual y hy fun u hu => ?_
    rw [cA_cA] at hu
    rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, idem_smul_half he.idem hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]

theorem placeModelExistsSum : ∀ D : D7, PlaceModelExistsSum D := by
  intro D ψ hψ S T ΛS ΛT hS hT P e he f₀ _ hvac
  have h := isOrthSum_of_isIdemSum he
  exact ⟨h.exists_model hψ hS hT he.2 hvac,
    h.conj.exists_model hψ hS hT (by rw [cA_cA, mul_comm, he.2]) hvac⟩

end GlobalTheory.PlaceModelSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.DefLift.BilFischer

variable {σ : Type} [Fintype σ]

def wt (α : σ →₀ ℕ) : ℂ := ∏ v, ((α v).factorial : ℂ)

theorem wt_ne_zero (α : σ →₀ ℕ) : wt α ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

theorem wt_add_single (α : σ →₀ ℕ) (v : σ) : wt (α + Finsupp.single v 1) = wt α * ((α v : ℂ) + 1) := by
  classical
  unfold wt
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v),
    ← Finset.mul_prod_erase _ (fun x => ((α x).factorial : ℂ)) (Finset.mem_univ v)]
  have h3 : ∏ x ∈ Finset.univ.erase v, (((α + Finsupp.single v 1 : σ →₀ ℕ) x).factorial : ℂ) =
      ∏ x ∈ Finset.univ.erase v, ((α x).factorial : ℂ) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxv : x ≠ v := Finset.ne_of_mem_erase hx
    simp [Finsupp.single_apply, Ne.symm hxv]
  rw [h3]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

def pair : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  (basisMonomials σ ℂ).constr ℂ fun α => wt α • lcoeff ℂ α

theorem pair_monomial_one (α : σ →₀ ℕ) (Q : MvPolynomial σ ℂ) :
    pair (monomial α 1) Q = wt α * AddMonoidAlgebra.coeff Q α := by
  have := (basisMonomials σ ℂ).constr_basis ℂ (fun α => wt α • lcoeff ℂ α) α
  rw [coe_basisMonomials] at this
  unfold pair
  rw [this]
  simp

theorem pair_monomial (α : σ →₀ ℕ) (c : ℂ) (Q : MvPolynomial σ ℂ) :
    pair (monomial α c) Q = c * (wt α * AddMonoidAlgebra.coeff Q α) := by
  have : (monomial α c : MvPolynomial σ ℂ) = c • monomial α 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply, pair_monomial_one, smul_eq_mul]

theorem pair_mul_X (P Q : MvPolynomial σ ℂ) (v : σ) : pair (P * X v) Q = pair P (pderiv v Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [X, monomial_mul, mul_one, pair_monomial, pair_monomial, coeff_pderiv, wt_add_single]
    ring
  | add P P' h h' => simp only [add_mul, map_add (f := _), LinearMap.add_apply, h, h']

def lin (A : σ → σ → ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun v => ∑ w, A v w • X w

theorem lin_X (A : σ → σ → ℂ) (v : σ) : lin A (X v) = ∑ w, A v w • X w := by
  simp [lin]

theorem pderiv_lin_X (A : σ → σ → ℂ) (v u : σ) : pderiv v (lin A (X u)) = C (A u v) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lin_X, map_sum, Finset.sum_eq_single v]
  · simp [smul_eq_C_mul]
  · intro w _ hw
    simp [pderiv_X, Pi.single_apply, hw]
  · simp

theorem pderiv_lin (A : σ → σ → ℂ) (v : σ) (Q : MvPolynomial σ ℂ) :
    pderiv v (lin A Q) = ∑ w, A w v • lin A (pderiv w Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp [lin]
  | add P P' h h' => simp only [map_add (f := _), h, h', smul_add, Finset.sum_add_distrib]
  | mul_X P u h =>
    rw [map_mul, Derivation.leibniz, h, pderiv_lin_X]
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, smul_add, Finset.sum_add_distrib,
      Finset.mul_sum, mul_smul_comm]
    congr 1
    rw [Finset.sum_eq_single u]
    · simp [smul_eq_C_mul, mul_comm]
    · intro w _ hw
      simp [pderiv_X, Pi.single_apply, hw, Ne.symm hw]
    · simp

theorem coeff_zero_lin (A : σ → σ → ℂ) (Q : MvPolynomial σ ℂ) : AddMonoidAlgebra.coeff (lin A Q) 0 = AddMonoidAlgebra.coeff Q 0 := by
  change constantCoeff (lin A Q) = constantCoeff Q
  induction Q using MvPolynomial.induction_on with
  | C c => simp [lin]
  | add P P' h h' => simp only [map_add (f := _), h, h']
  | mul_X P u h => simp [lin_X, map_sum, smul_eq_C_mul]

theorem pair_lin (A : σ → σ → ℂ) (P Q : MvPolynomial σ ℂ) :
    pair (lin A P) Q = pair P (lin (fun v w => A w v) Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    have : lin A (C c) = C c := by simp [lin]
    rw [this, C_apply, pair_monomial, pair_monomial, coeff_zero_lin]
  | add P P' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
  | mul_X P u h =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pair_mul_X, pderiv_lin, map_mul, lin_X, Finset.mul_sum, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mul_smul_comm, map_smul, map_smul, LinearMap.smul_apply, pair_mul_X, h]

theorem pair_nondeg (Q : MvPolynomial σ ℂ) (h : ∀ P, pair P Q = 0) : Q = 0 := by
  ext α
  have := h (monomial α 1)
  rw [pair_monomial_one] at this
  simpa [wt_ne_zero] using this

theorem pair_rep (ℓ : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (d : ℕ)
    (h : ∀ α : σ →₀ ℕ, d < α.degree → ℓ (monomial α 1) = 0) : ∃ Q, ∀ P, pair P Q = ℓ P := by
  classical
  have hfin : {α : σ →₀ ℕ | α.degree ≤ d}.Finite := Finsupp.finite_of_degree_le d
  refine ⟨∑ α ∈ hfin.toFinset, monomial α (ℓ (monomial α 1) / wt α), fun P => ?_⟩
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    have : (monomial α c : MvPolynomial σ ℂ) = c • monomial α 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [pair_monomial, this, map_smul, smul_eq_mul, coeff_sum]
    congr 1
    simp only [coeff_monomial, Finset.sum_ite_eq', Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    split_ifs with hd
    · exact mul_div_cancel₀ _ (wt_ne_zero α)
    · rw [h α (not_le.1 hd), mul_zero]
  | add P P' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']

open Classical in
theorem subst_eq_lin {ι : Type} [Fintype ι] {m n : ℕ} (a : ι → Matrix (Fin n) (Fin n) ℂ)
    (b : ι → Matrix (Fin m) (Fin m) ℂ) :
    subst a b = lin fun v w => if v.1 = w.1 then b v.1 w.2.1 v.2.1 * a v.1 v.2.2 w.2.2 else 0 := by
  unfold subst lin
  congr 1
  funext v
  rw [Fintype.sum_prod_type, Finset.sum_eq_single v.1, Fintype.sum_prod_type]
  · simp
  · intro τ _ hτ
    simp [Ne.symm hτ]
  · simp

theorem exists_pair (ι : Type) [Fintype ι] (m n : ℕ) :
    ∃ B : Pol ι m n →ₗ[ℂ] Pol ι m n →ₗ[ℂ] ℂ, (∀ Q, (∀ P, B P Q = 0) → Q = 0) ∧
      (∀ a b P Q, B (subst a b P) Q =
        B P (subst (fun τ => (a τ).transpose) (fun τ => (b τ).transpose) Q)) ∧
      ∀ (ℓ : Pol ι m n →ₗ[ℂ] ℂ) (d : ℕ),
        (∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → ℓ (MvPolynomial.monomial α 1) = 0) →
          ∃ Q, ∀ P, B P Q = ℓ P := by
  refine ⟨pair, pair_nondeg, fun a b P Q => ?_, pair_rep⟩
  rw [subst_eq_lin, subst_eq_lin, pair_lin]
  congr 3
  funext v w
  by_cases h : v.1 = w.1
  · simp [h]
  · simp [h, Ne.symm h]

end GlobalTheory.DefLift.BilFischer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousUnitaryRootExchangeMapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_unitaryRootExchangeMap : ∀ (D : D7) (B : HSp D) (η : AE D), η * cA D η = 0 → ∀ v : Fin B.rank → AE D, ∃ K : {y : Fin B.rank → AE D // η • y = y ∧ hA B v y = 0} → GA D B, Continuous K ∧ ∀ y, IsK B v y.1 (K y) := by
  first | exact @GlobalTheory.RootUnip.exists_continuous_isK | exact GlobalTheory.RootUnip.exists_continuous_isK | (intros; apply GlobalTheory.RootUnip.exists_continuous_isK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDegreeBoundOfRowUnitaryInvariantPairing
section
noncomputable section

open GlobalTheory.DefLift

namespace GlobalTheory.RowSupport

theorem exp_I_pow_injective : Function.Injective fun e : ℕ => Complex.exp Complex.I ^ e := by
  intro a b h
  simp only [← Complex.exp_nat_mul] at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have h2 : (a : ℝ) = b + k * (2 * Real.pi) := by
    have := congrArg Complex.im hk
    simpa using this
  by_cases h0 : k = 0
  · subst h0
    exact_mod_cast (by simpa using h2 : (a : ℝ) = b)
  · exfalso
    have h3 : (2 * k : ℤ) ≠ 0 := mul_ne_zero two_ne_zero h0
    refine (irrational_pi.intCast_mul h3).ne_int ((a : ℤ) - b) ?_
    push_cast
    linarith

def scal (m : ℕ) : Matrix.unitaryGroup (Fin m) ℂ :=
  ⟨Complex.exp Complex.I • 1, by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, mul_one]
    have : Complex.exp Complex.I * star (Complex.exp Complex.I) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp
    rw [this, one_smul]⟩

open Classical in
theorem rowSub_scal {ι : Type} [Fintype ι] {m n : ℕ} (τ : ι) (α : ι × Fin m × Fin n →₀ ℕ) :
    rowSub n τ (scal m) (MvPolynomial.monomial α 1) =
      Complex.exp Complex.I ^ (∑ v, if v.1 = τ then α v else 0) • MvPolynomial.monomial α 1 := by
  have hv : ∀ v : ι × Fin m × Fin n,
      (∑ i, ∑ c, ((if v.1 = τ then (scal m : Matrix (Fin m) (Fin m) ℂ) else 1) i v.2.1 *
        (1 : Matrix (Fin n) (Fin n) ℂ) v.2.2 c) • (MvPolynomial.X (v.1, i, c) : Pol ι m n)) =
      (if v.1 = τ then Complex.exp Complex.I else 1) • MvPolynomial.X v := by
    rintro ⟨ρ, j, d⟩
    by_cases h : ρ = τ
    · simp [h, scal, Matrix.one_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp [h, Matrix.one_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
  unfold rowSub subst
  rw [AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial, map_one, one_mul, MvPolynomial.monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp only [hv, smul_pow]
  rw [Finset.prod_smul, ← Finset.prod_pow_eq_pow_sum]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  split_ifs <;> simp

theorem exists_degree_bound (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X) (β : Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] ℂ)
    (h : ∀ τ u P x, β (rowSub n τ u P) (π τ u x) = β P x) :
    ∃ d : ℕ, ∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → β (MvPolynomial.monomial α 1) = 0 := by
  classical
  have hfin : ∀ τ, ∃ d : ℕ, ∀ e : ℕ,
      Module.End.HasEigenvalue (LinearMap.dualMap (π τ (scal m)) : Module.End ℂ (Module.Dual ℂ X))
        (Complex.exp Complex.I ^ e)⁻¹ → e ≤ d := by
    intro τ
    have h1 := Module.End.finite_hasEigenvalue (LinearMap.dualMap (π τ (scal m)) : Module.End ℂ (Module.Dual ℂ X))
    have h2 := h1.preimage (f := fun e : ℕ => (Complex.exp Complex.I ^ e)⁻¹)
      (inv_injective.comp exp_I_pow_injective).injOn
    obtain ⟨d, hd⟩ := h2.bddAbove
    exact ⟨d, fun e he => hd he⟩
  choose d hd using hfin
  refine ⟨∑ τ, d τ, fun α hα => ?_⟩
  by_contra hne
  have hdeg : α.degree = ∑ τ, ∑ v, if v.1 = τ then α v else 0 := by
    rw [Finset.sum_comm, Finsupp.degree_eq_sum]
    simp
  refine absurd hα (not_lt.2 ?_)
  rw [hdeg]
  refine Finset.sum_le_sum fun τ _ => hd τ _ ?_
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := β (MvPolynomial.monomial α 1)) ⟨?_, hne⟩
  rw [Module.End.mem_eigenspace_iff]
  ext x
  have := h τ (scal m) (MvPolynomial.monomial α 1) x
  rw [rowSub_scal, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  rw [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ (Complex.exp_ne_zero _))]
  convert this

end GlobalTheory.RowSupport

end
end

