module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SvalEqSumOfHasVal
section
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace SecValue

variable {K R : Type} [CommRing K] [CommRing R] {X Z : Scheme.{0}}

theorem res_constFn (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  exact congrArg (fun q : Γ(Sp K, ⊤) ⟶ Γ(X, V) => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (p.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)

theorem valR_constFn (p : X ⟶ Sp K) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, ← Category.comp_id (spMap f),
    HolHom.valR_spMap f (𝟙 _) ⊤ le_rfl, HolHom.valR_eq _ _ le_rfl]
  congr 1
  exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom a)
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id

def subComb (p : X ⟶ Sp K) {M : LB X} (s : M.Sec) {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) : M.Sec where
  f j := s.f j - ∑ i, constFn p _ (r i) * (σ i).f j
  compat j k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_sum, map_sum, mul_sub, s.compat j k, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (σ i).compat j k]
    ring

theorem valR_subComb (p : X ⟶ Sp K) {M : LB X} (s : M.Sec) {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec)
    (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : M.ι) (h : ⊤ ≤ q ⁻¹ᵁ M.U j) :
    valR q _ ((subComb p s r σ).f j) = valR q _ (s.f j) - ∑ i, f (r i) * valR q _ ((σ i).f j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← valR_constFn p f q hq _ h, HolHom.valR_eq _ _ h, subComb, map_sub, map_sum, map_mul]

theorem sval_subComb {L : LB Z} {π : X ⟶ Z} {m : ℕ} (p : X ⟶ Sp K) (s : SecP L π m) {n : ℕ} (r : Fin n → K)
    (σ : Fin n → SecP L π m) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : L.ι)
    (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ArcPts.sval (subComb p s r σ : SecP L π m) q j = ArcPts.sval s q j - ∑ i, f (r i) * ArcPts.sval (σ i) q j := by
  have hw : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) :=
    fun z hz => Set.mem_iInter.2 fun _ => h hz
  exact valR_subComb p s r σ f q hq (fun _ => j) hw

theorem sval_eq_zero {L : LB Z} {π : X ⟶ Z} {m : ℕ} (s : SecP L π m) (hs : ∀ i, s.f i = 0) (q : Sp R ⟶ X) (j : L.ι) :
    ArcPts.sval s q j = 0 := by
  refine (congrArg (valR q _) (hs fun _ => j)).trans ?_
  by_cases h : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j)
  · exact (HolHom.valR_eq q _ h 0).trans (map_zero _)
  · exact dif_neg h

end SecValue

theorem sval_eq_sum_of_hasVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A t y) (j : ℕ) [NeZero j] (s : SecP t.PP.L (pullback.fst t.G.hom y) j) (n : ℕ) (r : Fin n → ℂ⸨X⸩) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ), (∀ i, th i ∈ A.Theta j (α i)) → (∀ v, HasVal s (fib (Φ.x v)) (Φ.τ v) (∑ i, r i * A.FSum j (α i) (th i) v)) → ∀ (R : Type) [CommRing R] (f : ℂ⸨X⸩ →+* R) (q : Sp R ⟶ pullback t.G.hom y), q ≫ pullback.snd _ _ = spMap f → ∀ jj, ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U jj → sval s q jj = ∑ i, f (r i) * sval (Φ.sig j (α i) (th i)) q jj := by
  intro E _ _ _ H _ S A t y Φ j _ s n r α th hth hs R _ f q hq jj hjj
  have h0 := Φ.sep j (SecValue.subComb (pullback.snd t.G.hom y) s r fun i => Φ.sig j (α i) (th i)) fun v k hk => by
    have hv : fib (Φ.x v) ≫ pullback.snd t.G.hom y = spMap (RingHom.id _) := by
      rw [fib, pullback.lift_snd]
      exact (Spec.map_id _).symm
    rw [SecValue.sval_subComb _ s r _ _ _ hv k hk, hs v k hk, Finset.sum_mul, zero_mul, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Φ.val j (α i) (th i) (hth i) v k hk, RingHom.id_apply, _root_.mul_assoc]
  have h1 := SecValue.sval_eq_zero _ h0 q jj
  rwa [SecValue.sval_subComb _ s r _ f q hq jj hjj, sub_eq_zero] at h1

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaCharOffNeZeroDifferentiableQuasiPeriodic
section
noncomputable section

open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaBlock

variable {g : ℕ} {S : Finset (Fin g)}

def offEquiv (S : Finset (Fin g)) : {n : Fin g → ℤ // ∀ k ∈ S, n k = 0} ≃ ({k // k ∉ S} → ℤ) where
  toFun n i := n.1 i
  invFun l := ⟨fun k => if h : k ∈ S then 0 else l ⟨k, h⟩, fun k hk => dif_pos hk⟩
  left_inv n := by
    refine Subtype.ext (funext fun k => ?_)
    by_cases h : k ∈ S
    · simp [h, n.2 k h]
    · simp [h]
  right_inv l := by
    funext i
    simp [i.2]

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem submatrix_mem_siegelH_of_posDef_im (S : Finset (Fin g)) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    τ.submatrix (Subtype.val : {k // k ∉ S} → Fin g) Subtype.val ∈ _root_.ReciprocityTheory.PTheta.SiegelH {k // k ∉ S} := by
  unfold _root_.ReciprocityTheory.PTheta.SiegelH
  exact ⟨hs.submatrix _, hp.submatrix Subtype.val_injective⟩

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem ofReal_re_eq_self_of_eq_zero_or_half {c : ℂ} (h : c = 0 ∨ c = 1 / 2) :
    ((c.re : ℝ) : ℂ) = c := by
  rcases h with rfl | rfl
  · simp
  · apply Complex.ext <;> simp

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem dotProduct_eq_restrict_of_vanishing (S : Finset (Fin g)) {v : Fin g → ℂ}
    (hv : ∀ k ∈ S, v k = 0) (w : Fin g → ℂ) :
    v ⬝ᵥ w = (fun i : {k // k ∉ S} => v i) ⬝ᵥ (fun i : {k // k ∉ S} => w i) := by
  unfold dotProduct
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => k ∉ S)]
  have h0 : ∑ i : {k // ¬ k ∉ S}, v i * w i = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hv i (not_not.1 i.2), zero_mul]
  rw [h0, add_zero]

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem mulVec_restrict_eq_submatrix_mulVec_of_vanishing (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ)
    {v : Fin g → ℂ} (hv : ∀ k ∈ S, v k = 0) :
    (fun i : {k // k ∉ S} => (τ *ᵥ v) i) =
      τ.submatrix Subtype.val Subtype.val *ᵥ (fun i : {k // k ∉ S} => v i) := by
  funext i
  simp only [mulVec, submatrix_apply]
  rw [dotProduct_comm, dotProduct_eq_restrict_of_vanishing S hv, dotProduct_comm]

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem thetaCharOff_eq_theta_submatrix (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ)
    (c₁ c₂ : Fin g → ℂ) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hS : ∀ k ∈ S, c₁ k = 0) (z : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ z = _root_.ReciprocityTheory.PTheta.theta (fun i : {k // k ∉ S} => (c₁ i).re)
      (fun i : {k // k ∉ S} => (c₂ i).re) (fun i : {k // k ∉ S} => z i)
      (τ.submatrix Subtype.val Subtype.val) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff _root_.ReciprocityTheory.PTheta.theta _root_.ReciprocityTheory.PTheta.thetaTerm _root_.ReciprocityTheory.PTheta.eC _root_.ReciprocityTheory.PTheta.shiftVec _root_.ReciprocityTheory.PTheta.ofRealVec
  rw [← (_root_.GlobalTheory.ThetaBlock.offEquiv S).tsum_eq]
  congr 1
  funext n
  have hv : ∀ k ∈ S, ((fun i => ((n.1 i : ℤ) : ℂ)) + c₁) k = 0 := fun k hk => by
    simp [n.2 k hk, hS k hk]
  have hw : (fun i : {k // k ∉ S} =>
      (((_root_.GlobalTheory.ThetaBlock.offEquiv S n) i : ℤ) : ℂ) + (((c₁ i).re : ℝ) : ℂ)) =
      fun i : {k // k ∉ S} => ((fun i => ((n.1 i : ℤ) : ℂ)) + c₁) i := by
    funext i
    rw [ofReal_re_eq_self_of_eq_zero_or_half (h₁ i)]
    rfl
  have hz : (fun i : {k // k ∉ S} => z i) + (fun i : {k // k ∉ S} => (((c₂ i).re : ℝ) : ℂ)) =
      fun i : {k // k ∉ S} => (z + c₂) i := by
    funext i
    simp [ofReal_re_eq_self_of_eq_zero_or_half (h₂ i)]
  rw [hw, hz, dotProduct_eq_restrict_of_vanishing S hv (τ *ᵥ _), mulVec_restrict_eq_submatrix_mulVec_of_vanishing S τ hv,
    dotProduct_eq_restrict_of_vanishing S hv (z + c₂)]
  congr 1
  ring


open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
theorem _root_.GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic (g : ℕ) (S : Finset (Fin g))
    (τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2)
    (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) (hS : ∀ k ∈ S, c₁ k = 0) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ ≠ 0 ∧ Differentiable ℂ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂) ∧
      ∀ m n : Fin g → ℤ, (∀ k ∈ S, n k = 0) → ∃ a : ℂ, a ≠ 0 ∧ ∀ z,
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) =
          a * Complex.exp (-(2 * Real.pi * Complex.I) * ((fun i => (n i : ℂ)) ⬝ᵥ z)) *
            _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ z := by
  have hτ := submatrix_mem_siegelH_of_posDef_im S hs hp
  have hfun : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ = fun z => _root_.ReciprocityTheory.PTheta.theta (fun i : {k // k ∉ S} => (c₁ i).re)
      (fun i : {k // k ∉ S} => (c₂ i).re) (fun i : {k // k ∉ S} => z i)
      (τ.submatrix Subtype.val Subtype.val) :=
    funext (thetaCharOff_eq_theta_submatrix S τ c₁ c₂ h₁ h₂ hS)
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    obtain ⟨w, hw⟩ := Function.ne_iff.1
      (_root_.GlobalTheory.theta_ne_zero hτ (fun i : {k // k ∉ S} => (c₁ i).re)
        (fun i : {k // k ∉ S} => (c₂ i).re))
    apply hw
    have h := congrFun h0 (fun k => if h : k ∈ S then 0 else w ⟨k, h⟩)
    rw [hfun] at h
    have hr : (fun i : {k // k ∉ S} => (fun k => if h : k ∈ S then 0 else w ⟨k, h⟩) i.1) = w := by
      funext i
      simp [i.2]
    simp only [Pi.zero_apply] at h
    rwa [hr] at h
  · rw [hfun]
    exact (_root_.GlobalTheory.differentiable_theta hτ _ _).comp (by fun_prop)
  · intro m n hn
    set N : Fin g → ℂ := fun i => (n i : ℂ) with hN
    set M : Fin g → ℂ := fun i => (m i : ℂ) with hM
    have hsym : ∀ x y : Fin g → ℂ, x ⬝ᵥ τ *ᵥ y = y ⬝ᵥ τ *ᵥ x := by
      intro x y
      rw [dotProduct_mulVec, ← mulVec_transpose, hs.eq, dotProduct_comm]
    refine ⟨Complex.exp (2 * Real.pi * Complex.I * (c₁ ⬝ᵥ M) -
      Real.pi * Complex.I * (N ⬝ᵥ τ *ᵥ N) - 2 * Real.pi * Complex.I * (N ⬝ᵥ c₂)),
      Complex.exp_ne_zero _, fun z => ?_⟩
    let e : {p : Fin g → ℤ // ∀ k ∈ S, p k = 0} ≃ {p : Fin g → ℤ // ∀ k ∈ S, p k = 0} :=
      { toFun := fun p => ⟨p.1 - n, fun k hk => by simp [p.2 k hk, hn k hk]⟩
        invFun := fun p => ⟨p.1 + n, fun k hk => by simp [p.2 k hk, hn k hk]⟩
        left_inv := fun p => by ext; simp
        right_inv := fun p => by ext; simp }
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff
    rw [← e.tsum_eq, ← tsum_mul_left]
    congr 1
    funext p
    have hQ : (fun i => (((e p).1 i : ℤ) : ℂ)) = (fun i => ((p.1 i : ℤ) : ℂ)) - N := by
      funext i
      simp [e, hN]
    rw [hQ, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨∑ i, (p.1 i - n i) * m i, ?_⟩
    have hcast : ((∑ i, (p.1 i - n i) * m i : ℤ) : ℂ) =
        (fun i => ((p.1 i : ℤ) : ℂ)) ⬝ᵥ M - N ⬝ᵥ M := by
      simp [dotProduct, hM, hN, Finset.sum_sub_distrib, sub_mul]
    simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub, mulVec_add,
      mulVec_sub]
    linear_combination (Real.pi * Complex.I) * hsym (fun i => ((p.1 i : ℤ) : ℂ)) N +
      (Real.pi * Complex.I) * hsym c₁ N - (2 * Real.pi * Complex.I) * hcast

end GlobalTheory.ThetaBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSumShift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem isFShift_iff {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (k : ℕ) [NeZero k] (α : A.X)
    (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) (F : ℂ⸨X⸩)
    (hd : (k : ℤ) ∣ A.be la.y α := by apply_assumption) :
    IsFShift A k α th la z F ↔ F = A.FSumShift k α th la z := by
  have key : ∀ n : ℤ, (∑ᶠ (m : A.X) (_ : A.exponent k (α + la.y) m + A.be la.y α / k = n),
      A.term k α th m (z + (k : ℂ)⁻¹ • A.P0 la)) = (A.FSumShift k α th la z).coeff n := fun n => by
    rw [AnArc.coeff_FSumShift]
    refine finsum_cond_eq_sum_of_cond_iff _ fun {m} _ => ?_
    rw [AnArc.mem_level, eq_sub_iff_add_eq]
  unfold IsFShift
  simp only [key]
  exact ⟨fun h => HahnSeries.ext (funext h.2), fun h => ⟨⟨NeZero.ne k, hd⟩, fun n => by rw [h]⟩⟩

theorem theta_sum_shift : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∀ (k : ℕ) [NeZero k] (la : A.La), (∀ α, (k : ℤ) ∣ A.be la.y α) → ∃ cz : A.V → ℂ, (∀ z, cz z ≠ 0) ∧ ∀ α, ∀ th ∈ A.Theta k α, ∃ th' ∈ A.Theta k (α + la.y), (th ≠ 0 → th' ≠ 0) ∧ ∀ z, (∀ F, IsFShift A k α th la z F ↔ F = HahnSeries.single (A.be la.y α / k) (cz z) * A.FSum k (α + la.y) th' z) ∧ ∀ w : ℂ, A.Sum k α th w (z + (k : ℂ)⁻¹ • A.Pw w la) = cz z * eTwoPi (w * ((A.be la.y α / k : ℤ) : ℂ)) * A.Sum k (α + la.y) th' w z := by
  intro O _ _ A k _ la hla
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  refine ⟨fun z => Complex.exp (A.lin la z), fun z => Complex.exp_ne_zero _, fun α th hth =>
    ⟨A.shift k la α th, A.shift_mem_Theta hth la, fun h h' => h ?_, fun z => ⟨fun F => ?_, fun w => ?_⟩⟩⟩
  · exact A.shift_injective k la α (h'.trans (map_zero _).symm)
  · rw [isFShift_iff A k α th la z F (hla α), A.FSumShift_eq k la (Int.mul_ediv_cancel' (hla α)).symm]
  · obtain ⟨m, hm⟩ := hla α
    rw [A.Sum_add_Pw_div, hm, Int.mul_ediv_cancel_left _ (NeZero.ne (k : ℤ))]
    congr 3
    push_cast
    field_simp

end GlobalTheory.ArcPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusCoordinateRatioDifferentiableAtOrigin
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
open Filter Topology

namespace GlobalTheory.AbelianLetters

theorem exists_top_le_wchart {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Sp ℂ ⟶ X)) : ∃ j, ⊤ ≤ LB.wchart L φ j := by
  choose j hj using fun k => exists_chart hL (φ k (default : PrimeSpectrum ℂ))
  refine ⟨j, fun p _ => Set.mem_iInter.2 fun k => ?_⟩
  obtain rfl : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hj k

theorem valAt'_unit_ne_zero {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    valAt' x U f.val ≠ 0 := by
  rw [HolHom.valAt'_eq_valR, HolHom.valR_eq _ _ h]
  exact (f.isUnit.map _).ne_zero

theorem IsRatio.differentiableAt_zero : ∀ [Algebra (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (s₀ : Out.GtPt D D.P.A), s₀.b = 𝟙 D.P.A ^ n → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n s₀ u → ∀ x, DifferentiableAt ℂ (u x) 0 := by
  intro _ D g n ex s₀ hb hadd hol hchi u hu x
  obtain ⟨j, hj⟩ := exists_top_le_wchart D.P.isLB (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • 0)).b x)
  have h1 : ∀ z, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j ↔
      ⊤ ≤ (show Sp ℂ ⟶ _ from (ex z).b.left) ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A (𝟙 D.P.A ^ 1) x) j := by
    intro z
    have := top_le_wchart_nsmul hadd (n := 1) rfl z x j
    rwa [Nat.cast_one, one_smul] at this
  have hS : {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j} ∈ 𝓝 ((n : ℂ) • (0 : Fin g → ℂ)) := by
    filter_upwards [(HolHom.holAt_of_isHolTo hol (Set.mem_univ ((n : ℂ) • (0 : Fin g → ℂ))) _ ((h1 _).1 hj)).1]
      with t ht using (h1 t).2 ht
  have hn : DifferentiableAt ℂ (fun z : Fin g → ℂ => (n : ℂ) • z) 0 := by fun_prop
  have hc : DifferentiableAt ℂ (fun z => chiVal (ex ((n : ℂ) • z)) x j) 0 :=
    ((hchi x j).differentiableAt hS).comp 0 hn
  have h0 := (top_le_wchart_nsmul hadd hb 0 x j).1 hj
  obtain ⟨hev, hd⟩ := HolHom.holAt_of_isHolTo hol (Set.mem_univ 0) _ h0
  refine (hc.fun_mul ((hd ((s₀.s x).s j).val).fun_inv (valAt'_unit_ne_zero _ h0 _))).congr_of_eventuallyEq ?_
  filter_upwards [hev] with t ht
  exact (eq_mul_inv_iff_mul_eq₀ (valAt'_unit_ne_zero _ ht _)).2
    (hu x t j ((top_le_wchart_nsmul hadd hb t x j).2 ht)).symm

end GlobalTheory.AbelianLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusCoordinateRatioEqTorusCoordOverOrigin
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor CategoryTheory.MonObj GlobalTheory.AbelianLetters

namespace GlobalTheory.AbelianLetters.TorusRatio

theorem valR_of_corr_one {A : Type} [CommRing A] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {ε : K → ℤ}
    {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (h : LB.Gen.Corr L _ _ _ _ t (LB.oneGen L))
    (x : Sp A ⟶ Y) (j : K → L.ι) (hj : LB.Coh L φ j) (hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j) :
    valR x (LB.wchart L φ j) (t.s j).val = 1 := by
  have e := h j PEmpty.elim hj (fun k => k.elim) (fun _ k => k.elim)
  have hx' : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim) :=
    fun y hy => ⟨hx hy, Set.mem_iInter.2 fun k => k.elim⟩
  have e1 : res (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim ≤ _)
      (t.s j) = 1 := e.trans (map_one _)
  refine (HolHom.valR_res x inf_le_left _ hx').symm.trans ?_
  refine (congrArg (fun q => valR x _ q.val) e1).trans ?_
  exact (HolHom.valR_eq x _ hx' _).trans (map_one _)

theorem isZero_of_isAdd {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R} {T : Over (Sp R)}
    {g : Out.GtPt D T} (hb : g.b = 1) (h : Out.GtPt.IsAdd g g g) (χ : D.X) :
    LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.oneGen D.P.L) := by
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    ((val_corr hJ (h.2 χ) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c1 : TorusCoord.cubVal (𝟙 _ ≫ (lift (Out.DegPre.cT D T χ) (lift g.b g.b)).left) y J = 1 := by
    rw [Category.id_comp, hb]
    exact (isCub_cubV D.cub hJ).face₂ _ _
  have e2 := (congrArg (val (g.s χ) (𝟙 _) y J * ·) c1).symm.trans e
  rw [_root_.mul_one] at e2
  exact (mul_eq_left.1 e2.symm).trans (val_one _).symm

theorem ratio_eq_torus_coord [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ)
    (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt)
    (hb : ∀ Tt b, (sB Tt b).b = b ^ n)
    (hadd : ∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b')))
    (hpull : ∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b)))
    (hex : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) :
    (∀ p : Out.GtPtF D ℂ, p.IsZero → IsTorusPt p (fun _ => 1)) ∧
      ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → ∀ (z : Fin g → ℂ) (xv : D.X → ℂ),
        (ex z).b = Out.DegPre.zeroF D ℂ → IsTorusPt (ex ((n : ℂ) • z)) xv → ∀ x, u x z = xv x := by
  refine ⟨fun p hp => ⟨hp.1, fun χ j hj hc => valR_of_corr_one (hp.2 χ) (𝟙 (Sp ℂ)) j hj hc⟩,
    fun u hu z xv hz ht x => ?_⟩
  have hz1 : (ex z).b = 1 := hz
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (Z := Sp ℂ) (IsLocalRing.closedPoint ℂ)
  have hs : (sB (Out.TF (R := ℂ) ℂ) 1).b = (ex ((n : ℂ) • z)).b := by
    rw [hb, b_nsmul hex, hz1]
  let j : Fin 4 → D.P.L.ι := fun k => J (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x k)
  have hj : LB.Coh D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x) j := fun _ _ e => congrArg J e
  have hc : ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x) j := fun y _ =>
    Set.mem_iInter.2 fun k => by
      obtain rfl : y = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      exact hJ _
  have h1 := hu x z j hc
  rw [ht.2 x j hj hc] at h1
  have hp := hpull D.P.A (Out.TF (R := ℂ) ℂ) (ex z).b (𝟙 _)
  have ha := hadd (Out.TF (R := ℂ) ℂ) 1 1
  rw [_root_.mul_one] at ha
  have e1 : (ex z).b ≫ 𝟙 D.P.A = 1 := (Category.comp_id _).trans hz1
  rw [e1] at hp
  have h2 := valR_of_isPull (A := ℂ) (p := (Out.TF (R := ℂ) ℂ).hom) hp x j
  have h3 := valR_of_corr_one (isZero_of_isAdd ((hb _ _).trans (one_pow n)) ha x) (𝟙 (Sp ℂ)) j
    (by rw [hs]; exact hj) (by rw [hs]; exact hc)
  have h4 := h2.symm.trans h3
  exact ((congrArg (u x z * ·) h4).trans (_root_.mul_one _)).symm.trans h1.symm

end GlobalTheory.AbelianLetters.TorusRatio
end
end

