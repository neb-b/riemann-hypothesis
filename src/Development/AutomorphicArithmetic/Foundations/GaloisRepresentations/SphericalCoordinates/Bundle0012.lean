module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEigSame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.SameEigenvalues

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} {β : G.Cˣ}

private theorem toV_mul (y y' : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    ((GlobalTheory.LKCx.toV G v β (y * y') : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z =
      (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
        ((GlobalTheory.LKCx.toV G v β y' : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]

private theorem toV_inv_cancel (y : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    (GlobalTheory.LKCx.toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
      ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
    Matrix.one_mulVec]

private theorem same_symm {x : (AfP p ⊗[ℚ] G.C)ˣ} {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t}
    {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)} {a b : GlobalTheory.LKCx.Dat G v β}
    (h : GlobalTheory.LKCx.Same G v β x t hx Kf K' a b) : GlobalTheory.LKCx.Same G v β x t hx Kf K' b a := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  refine ⟨y⁻¹, k⁻¹, c⁻¹, inv_mem hk1, inv_mem hk2, inv_ne_zero hc, ?_, ?_⟩
  · rw [h1, map_inv, map_inv, ← Prod.inv_mk]
    group
  · rw [h2, Matrix.mulVec_smul, toV_inv_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem same_trans {x : (AfP p ⊗[ℚ] G.C)ˣ} {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t}
    {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)} {a b d : GlobalTheory.LKCx.Dat G v β}
    (h : GlobalTheory.LKCx.Same G v β x t hx Kf K' a b) (h' : GlobalTheory.LKCx.Same G v β x t hx Kf K' b d) :
    GlobalTheory.LKCx.Same G v β x t hx Kf K' a d := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  obtain ⟨y', k', c', hk1', hk2', hc', h1', h2'⟩ := h'
  refine ⟨y' * y, k * k', c' * c, mul_mem hk1 hk1', mul_mem hk2 hk2', mul_ne_zero hc' hc, ?_, ?_⟩
  · rw [h1', h1, map_mul, map_mul]
    simp only [← Prod.mk_mul_mk, _root_.mul_assoc]
  · rw [h2', h2, Matrix.mulVec_smul, toV_mul, smul_smul]

private theorem minpoly_conj {F C : Type} [Field F] [Ring C] [Algebra F C] (u : Cˣ) (x : C) :
    minpoly F ((u : C) * x * ((u⁻¹ : Cˣ) : C)) = minpoly F x := by
  let e : C ≃ₐ[F] C :=
    { toFun := fun w => (u : C) * w * ((u⁻¹ : Cˣ) : C)
      invFun := fun w => ((u⁻¹ : Cˣ) : C) * w * (u : C)
      left_inv := fun w => by simp [_root_.mul_assoc]
      right_inv := fun w => by simp [_root_.mul_assoc]
      map_mul' := fun w w' => by simp [_root_.mul_assoc]
      map_add' := fun w w' => by simp [mul_add, add_mul]
      commutes' := fun r => by
        show (u : C) * algebraMap F C r * ((u⁻¹ : Cˣ) : C) = algebraMap F C r
        rw [← Algebra.commutes, _root_.mul_assoc, Units.mul_inv, _root_.mul_one] }
  exact minpoly.algEquiv_eq e x

private theorem posV_ne (z : GlobalTheory.LKCx.PosV G v β) : z.1 ≠ 0 := by
  intro h
  have := z.2
  rw [h] at this
  simp at this

private theorem eigL_eq {y : GlobalTheory.LKCx.grp G β} {z : Fin G.n → ℂ} {e : ℂ} (hz : z ≠ 0)
    (h : (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = e • z) :
    GlobalTheory.RootSumWeights.eigL G v β y z = e := by
  have hf : GlobalTheory.LKCx.FixL G v β y z := ⟨e, h⟩
  unfold GlobalTheory.RootSumWeights.eigL
  rw [dite_eq_left hf]
  have hs := hf.choose_spec
  exact smul_left_injective ℂ hz (hs.symm.trans h)

private theorem conj_eig (y₀ y : GlobalTheory.LKCx.grp G β) (c e : ℂ) (hc : c ≠ 0) (z : Fin G.n → ℂ) :
    (GlobalTheory.LKCx.toV G v β (y₀ * y * y₀⁻¹) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
                 (c • ((GlobalTheory.LKCx.toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) =
      e • (c • ((GlobalTheory.LKCx.toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) ↔
    (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = e • z := by
  rw [Matrix.mulVec_smul, toV_mul, toV_mul, toV_inv_cancel, smul_comm e c,
    ← Matrix.mulVec_smul _ e z]
  constructor
  · intro h
    have h' := smul_right_injective (Fin G.n → ℂ) hc h
    have h'' := congrArg (fun w => (GlobalTheory.LKCx.toV G v β y₀⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) h'
    simpa only [toV_inv_cancel] using h''
  · intro h
    rw [h]

end UpperTheory.Gal.W2.SameEigenvalues

open UpperTheory.Gal.W2.SameEigenvalues in
theorem UpperTheory.Gal.W2.eigSame_of :
    UpperTheory.Gal.W2.EigSame := by
  intro p _ G v c B K S hS a a' hq
  have hE := Quot.eqvGen_exact hq
  have hsame := (Equivalence.eqvGen_iff ⟨fun _ => GlobalTheory.LKCx.same_refl _ _ _ _ _ _ _ _ _,
    fun h => same_symm h, fun h h' => same_trans h h'⟩).mp hE
  obtain ⟨y₀, k, d, hk1, hk2, hd, h1, h2⟩ := hsame
  refine ⟨(MulAut.conj y₀).toEquiv, by simp, fun y => ?_⟩
  have hA : a'.1.1 = B.toAf y₀ * a.1.1 * k.1 := congrArg Prod.fst h1
  have hP : a'.1.2 = GlobalTheory.LKCx.toP1 G B.β y₀ * a.1.2 * k.2 := congrArg Prod.snd h1
  have hV : a'.2.1 =
      d • ((GlobalTheory.LKCx.toV G v B.β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1) := h2
  have hFix : GlobalTheory.LKCx.FixL G v B.β (y₀ * y * y₀⁻¹) a'.2.1 ↔ GlobalTheory.LKCx.FixL G v B.β y a.2.1 := by
    unfold GlobalTheory.LKCx.FixL
    rw [hV]
    exact exists_congr fun e => conj_eig y₀ y d e hd a.2.1
  have hAf : a'.1.1⁻¹ * B.toAf (y₀ * y * y₀⁻¹) * a'.1.1 ∈ S ↔ a.1.1⁻¹ * B.toAf y * a.1.1 ∈ S := by
    rw [hA, map_mul, map_mul, map_inv]
    have : (B.toAf y₀ * a.1.1 * k.1)⁻¹ * (B.toAf y₀ * B.toAf y * (B.toAf y₀)⁻¹) *
        (B.toAf y₀ * a.1.1 * k.1) = k.1⁻¹ * (a.1.1⁻¹ * B.toAf y * a.1.1) * k.1 := by group
    rw [this]
    exact hS k.1 hk1 _
  have hP1 : a'.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β (y₀ * y * y₀⁻¹) * a'.1.2 ∈ KHT p G.m G.n 1 G.Fw ↔
      a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2 ∈ KHT p G.m G.n 1 G.Fw := by
    rw [hP, map_mul, map_mul, map_inv]
    have : (GlobalTheory.LKCx.toP1 G B.β y₀ * a.1.2 * k.2)⁻¹ *
        (GlobalTheory.LKCx.toP1 G B.β y₀ * GlobalTheory.LKCx.toP1 G B.β y * (GlobalTheory.LKCx.toP1 G B.β y₀)⁻¹) *
        (GlobalTheory.LKCx.toP1 G B.β y₀ * a.1.2 * k.2) =
        k.2⁻¹ * (a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2) * k.2 := by group
    rw [this]
    constructor
    · intro hm
      have h3 := mul_mem (mul_mem hk2 hm) (inv_mem hk2)
      simpa [_root_.mul_assoc] using h3
    · intro hm
      exact mul_mem (mul_mem (inv_mem hk2) hm) hk2
  have hSees : Sees B S a' (y₀ * y * y₀⁻¹) ↔ Sees B S a y := and_congr hFix (and_congr hAf hP1)
  refine ⟨hSees.symm, fun hs => ⟨?_, ?_⟩⟩
  · show minpoly G.F (((y₀ * y * y₀⁻¹ : GlobalTheory.LKCx.grp G B.β) : G.Cˣ × ℚˣ).1 : G.C) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, Units.val_mul]
    exact minpoly_conj _ _
  · obtain ⟨e, he⟩ := hs.1
    rw [eigL_eq (posV_ne a.2) he]
    apply eigL_eq (posV_ne a'.2)
    rw [hV]
    exact (conj_eig y₀ y d e hd a.2.1).mpr he
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFixFinite
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.CechDR GlobalTheory.HodgeCoh KaehlerDifferential GlobalTheory.Points

namespace UpperTheory.Gal.W2

private theorem iso_alg {R : Type} [CommRing R] [Algebra ℂ R] [IsNoetherianRing R] {d : ℕ}
    (e : R →ₐ[ℂ] ℂ) (φ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ))
    (hk : ∀ ω : Ω[R⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → R) (ω' : Fin m → Ω[R⁄ℂ]),
      (∀ i, e (b i) = 0) ∧ ω = ∑ i, b i • ω' i)
    (g : Fin d → R) (hg : ∀ j, e (g j) = 0) (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ j, φ (D ℂ R (g j)) = M j) (hdet : M.det ≠ 0) :
    ∃ r : R, e r = 1 ∧ ∀ e' : R →ₐ[ℂ] ℂ, (∀ j, e' (g j) = 0) → e' r ≠ 0 → e' = e := by
  classical
  set m : Ideal R := RingHom.ker e with hm
  set Ig : Ideal R := Ideal.span (Set.range g) with hIgEq
  have hmem : ∀ x, x ∈ m ↔ e x = 0 := fun x => RingHom.mem_ker
  have hsub : ∀ x : R, x - algebraMap ℂ R (e x) ∈ m := fun x => by
    rw [hmem, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  let dl : R →ₗ[ℂ] R ⧸ m ^ 2 :=
    { toFun := fun x => Ideal.Quotient.mk (m ^ 2) (x - algebraMap ℂ R (e x))
      map_add' := fun x y => by
        simp only [map_add (f := _), map_sub]
        ring
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, map_sub, AlgHom.commutes,
          Ideal.Quotient.mk_algebraMap, Algebra.algebraMap_self]
        ring }
  let dd : Derivation ℂ R (R ⧸ m ^ 2) := Derivation.mk' dl (fun a b => by
    simp only [dl, LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    rw [← map_mul, ← map_mul, ← map_add (f := _), Ideal.Quotient.eq]
    have h2 : (a - algebraMap ℂ R (e a)) * (b - algebraMap ℂ R (e b)) ∈ m ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (hsub a) (hsub b)
    convert (m ^ 2).neg_mem_iff.mpr h2 using 1
    simp only [map_mul]
    ring)
  have hd : ∀ x, dd x = Ideal.Quotient.mk (m ^ 2) (x - algebraMap ℂ R (e x)) := fun x => rfl
  have hL : ∀ x, dd.liftKaehlerDifferential (D ℂ R x) = dd x := fun x =>
    Derivation.liftKaehlerDifferential_comp_D dd x
  have hkill : ∀ b ∈ m, ∀ ω, b • dd.liftKaehlerDifferential ω = 0 := by
    intro b hb
    have hz : (b • dd.liftKaehlerDifferential : Ω[R⁄ℂ] →ₗ[R] R ⧸ m ^ 2) = 0 := by
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun x => ?_)
      show (b • dd.liftKaehlerDifferential) (D ℂ R x) = (0 : Ω[R⁄ℂ] →ₗ[R] R ⧸ m ^ 2) (D ℂ R x)
      rw [LinearMap.smul_apply, LinearMap.zero_apply, hL, hd, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
      exact Ideal.mul_mem_mul hb (hsub x)
    intro ω
    exact LinearMap.congr_fun hz ω
  have hle : m ≤ Ig ⊔ m ^ 2 := by
    intro x hx
    set c : Fin d → ℂ := Matrix.vecMul (φ (D ℂ R x)) M⁻¹ with hcEq
    have hc : ∑ j, c j • M j = φ (D ℂ R x) := by
      have h1 : Matrix.vecMul c M = φ (D ℂ R x) := by
        rw [hcEq, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
          Matrix.vecMul_one]
      rw [← h1]
      funext l
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    set x' := x - ∑ j, c j • g j with hx'Eq
    have hx' : φ (D ℂ R x') = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hx'Eq, map_sub, map_sum, Derivation.map_smul, map_smul, hM, hc, sub_self]
    obtain ⟨k, b, ω', hb, hω⟩ := hk _ hx'
    have hx'm : x' ∈ m ^ 2 := by
      have h1 : dd.liftKaehlerDifferential (D ℂ R x') = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hω, map_sum]
        exact Finset.sum_eq_zero fun i _ => by
          rw [map_smul]
          exact hkill _ ((hmem _).mpr (hb i)) _
      have hex' : e x' = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp [hx'Eq, map_sub, map_sum, map_smul, hg, (hmem x).mp hx]
      rw [hL, hd, hex', map_zero, sub_zero, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact h1
    have hsum : ∑ j, c j • g j ∈ Ig :=
      Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ (c j) (Ideal.subset_span ⟨j, rfl⟩)
    have hx : x = ∑ j, c j • g j + x' := by
      rw [hx'Eq]
      abel
    rw [hx]
    exact Submodule.add_mem_sup hsum hx'm
  have hfg : (Submodule.map (Submodule.mkQ Ig) m).FG := (IsNoetherian.noetherian m).map _
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
    (Submodule.map (Submodule.mkQ Ig) m) hfg (by
      rw [← Submodule.map_smul'']
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi, q, hq, hiq⟩ := Submodule.mem_sup.mp (hle hx)
      refine ⟨q, ?_, ?_⟩
      · rw [pow_two, ← Ideal.smul_eq_mul] at hq
        exact hq
      · rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hiq]
        have : q - (i + q) = -i := by abel
        rw [this]
        exact Ig.neg_mem hi)
  refine ⟨r, ?_, ?_⟩
  · have h := (hmem _).mp hr1
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h
  · intro e' he' hr'
    have hIg : Ig ≤ RingHom.ker e' := Ideal.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      exact he' j)
    have hmk : ∀ x ∈ m, e' x = 0 := by
      intro x hx
      have h0 := hr _ (Submodule.mem_map_of_mem hx)
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul] at h0
      have h3 := hIg h0
      rw [RingHom.mem_ker, map_mul] at h3
      exact (mul_eq_zero.mp h3).resolve_left hr'
    ext x
    have h := hmk _ (hsub x)
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h
    exact h

private theorem ev_pull {Z Y : Scheme.{0}} {sZ : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} {c : Y ⟶ Z}
    {U : Z.Opens} {V : Y.Opens} (hV : V ≤ c ⁻¹ᵁ U) {y : CxPts s' (RingHom.id ℂ)}
    (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) (f : Sec sZ U) :
    CxPts.ev s' (RingHom.id ℂ) V (Sec.res s' hV (appSec sZ s' c U f)) y = valR (y.1 ≫ c) U f :=
  (CxPts.ev_res hV hy _).trans (valR_comp _ _ _ _).symm

private def evAlg {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} {V : Y.Opens} {y : CxPts s' (RingHom.id ℂ)}
    (h : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) : Sec s' V →ₐ[ℂ] ℂ :=
  { (CxPts.evHom h : Sec s' V →+* ℂ) with
    commutes' := fun a => by
      have := CxPts.ev_algX h a
      rw [CxPts.ev_eq h] at this
      exact this }

private theorem evAlg_apply {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} {V : Y.Opens} {y : CxPts s' (RingHom.id ℂ)}
    (h : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) (f : Sec s' V) :
    evAlg h f = CxPts.ev s' (RingHom.id ℂ) V f y := (CxPts.ev_eq h f).symm

private theorem eq_of_evAlg {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} {V : Y.Opens} (hV : IsAffineOpen V)
    {y y' : CxPts s' (RingHom.id ℂ)} (h : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V)
    (h' : y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) (e : evAlg h' = evAlg h) : y' = y := by
  apply Subtype.ext
  rw [← specMap_valMap_fromSpec hV y'.1 h', ← specMap_valMap_fromSpec hV y.1 h]
  congr 2
  ext f
  exact congrArg (fun φ => φ f) e

private theorem isolated {Z Y : Scheme.{0}} {sZ : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} {d : ℕ} {c₁ c₂ : Y ⟶ Z}
    {h₁ : c₁ ≫ sZ = s'} {h₂ : c₂ ≫ sZ = s'} [IsLocallyNoetherian Y] (y : CxPts s' (RingHom.id ℂ))
    (hfix : y.1 ≫ c₁ = y.1 ≫ c₂) {A : Matrix (Fin d) (Fin d) ℂ}
    (hT : GlobalTheory.W1.IsTan d c₁ c₂ h₁ h₂ y A) (hdet : (1 - A).det ≠ 0) :
    ∃ W : Y.Opens, y ∈ CxPts.ptsIn s' (RingHom.id ℂ) W ∧
      ∀ y' : CxPts s' (RingHom.id ℂ), y'.1 ≫ c₁ = y'.1 ≫ c₂ →
        y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) W → y' = y := by
  obtain ⟨U, V, hV1, hV2, t, hyV, hU, hVa, φ, hφs, hφ1, hφ2, hφk⟩ := hT
  haveI : IsNoetherianRing (Sec s' V) := IsLocallyNoetherian.component_noetherian ⟨V, hVa⟩
  let g : Fin d → Sec s' V := fun j =>
    Sec.res s' hV1 (appSec sZ s' c₁ U (t j)) - Sec.res s' hV2 (appSec sZ s' c₂ U (t j))
  have hgz : ∀ (y' : CxPts s' (RingHom.id ℂ)) (hy' : y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) V),
      y'.1 ≫ c₁ = y'.1 ≫ c₂ → ∀ j, evAlg hy' (g j) = 0 := by
    intro y' hy' hf j
    simp only [g, map_sub, evAlg_apply, ev_pull hV1 hy', ev_pull hV2 hy', hf, sub_self]
  have hk : ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V)
      (ω' : Fin m → Ω[Sec s' V⁄ℂ]), (∀ i, evAlg hyV (b i) = 0) ∧ ω = ∑ i, b i • ω' i := by
    intro ω hω
    obtain ⟨m, b, ω', hb, hsum⟩ := hφk ω hω
    exact ⟨m, b, ω', fun i => by rw [evAlg_apply]; exact hb i, hsum⟩
  have hM : ∀ j, φ (D ℂ (Sec s' V) (g j)) = (1 - A) j := by
    intro j
    simp only [g, map_sub, hφ1, hφ2]
    funext l
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  obtain ⟨r, hr1, hr⟩ := iso_alg (evAlg hyV) φ hk g (hgz y hyV hfix) (1 - A) hM hdet
  refine ⟨Y.basicOpen r, ?_, ?_⟩
  · refine (CxPts.mem_ptsIn_basicOpen hyV r).mpr ?_
    rw [← evAlg_apply hyV, hr1]
    exact one_ne_zero
  · intro y' hf hy'
    have hy'V : y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) V := CxPts.ptsIn_mono (Y.basicOpen_le r) hy'
    have hne : evAlg hy'V r ≠ 0 := by
      rw [evAlg_apply]
      exact (CxPts.mem_ptsIn_basicOpen hy'V r).mp hy'
    exact eq_of_evAlg hVa hyV hy'V (hr _ (hgz y' hy'V hf) hne)

theorem fixFinite_of : FixFinite := by
  intro Z Y sZ s' d c₁ c₂ h₁ h₂ _ _ _ hiso
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s'
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s'
  haveI : IsNoetherian Y := {}
  set F := {y : CxPts s' (RingHom.id ℂ) | y.1 ≫ c₁ = y.1 ≫ c₂} with hF
  have hW : ∀ y : F, ∃ W : Y.Opens, y.1 ∈ CxPts.ptsIn s' (RingHom.id ℂ) W ∧
      ∀ y' : CxPts s' (RingHom.id ℂ), y'.1 ≫ c₁ = y'.1 ≫ c₂ →
        y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) W → y' = y.1 := by
    intro y
    obtain ⟨A, hT, hdet⟩ := hiso y.1 y.2
    exact isolated y.1 y.2 hT hdet
  choose W hyW hW' using hW
  have hcov : (fun y : CxPts s' (RingHom.id ℂ) => (y : Sp ℂ ⟶ Y) (IsLocalRing.closedPoint ℂ)) '' F ⊆
      ⋃ i : F, (W i : Set Y) := by
    rintro _ ⟨y, hy, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, CxPts.mem_ptsIn.mp (hyW ⟨y, hy⟩)⟩
  obtain ⟨t, ht⟩ := (TopologicalSpace.NoetherianSpace.isCompact _).elim_finite_subcover
    (fun i : F => (W i : Set Y)) (fun i => (W i).isOpen) hcov
  refine (t.finite_toSet.image Subtype.val).subset ?_
  intro y' hy'
  obtain ⟨i, hi, hmem⟩ := Set.mem_iUnion₂.mp (ht ⟨y', hy', rfl⟩)
  exact ⟨i, hi, (hW' i y' hy' (CxPts.mem_ptsIn.mpr hmem)).symm⟩

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFixLine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem herm_pos_toV_mulVec_of_pos {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y : LKCx.grp G β) (z : Fin G.n → ℂ) (hz : 0 < (star z ⬝ᵥ LKCx.herm G v β *ᵥ z).re) :
    0 < (star (↑(LKCx.toV G v β y) *ᵥ z) ⬝ᵥ LKCx.herm G v β *ᵥ (↑(LKCx.toV G v β y) *ᵥ z)).re := by
  have hM : (↑(LKCx.toV G v β y) : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v ↑(↑y : G.Cˣ × ℚˣ).1 := rfl
  have hs := GlobalTheory.ArchBound.herm_sim G β y v
  have hpos : (0 : ℝ) < ((↑(↑y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) := by exact_mod_cast y.2.2
  rw [hM, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hs, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_pos hpos hz

private theorem actY_actY_inv {p : ℕ} [Fact p.Prime] {D : UPel.HT.Datum p} {G : HTGroup p} (L : Link D G)
    {β : G.Cˣ} (a : LKCx.grp G β) (w : VQ D) : actY L a (actY L a⁻¹ w) = w := by
  show L.rep _ (L.rep _ w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  have h1 : ((↑(↑a : G.Cˣ × ℚˣ).1 : G.C) * ↑(↑a⁻¹ : G.Cˣ × ℚˣ).1) = 1 := by
    rw [← Units.val_mul, ← Prod.fst_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Prod.fst_one,
      Units.val_one]
  rw [h1, map_one, Module.End.one_apply]

theorem UpperTheory.Gal.W2.fixLine_of :
    UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.FixLine := by
  intro hA
  unfold ActY at hA
  unfold FixLine
  intro p _ D G L v t₀ ρ β RD Q z hQ hrel y
  have hz0 : z.1 ≠ 0 := by
    intro h0
    have h1 := z.2
    rw [h0] at h1
    simp at h1
  have hinvmul : ∀ (y' : LKCx.grp G β) (x : Fin G.n → ℂ),
      (LKCx.toV G v β y'⁻¹).val *ᵥ ((LKCx.toV G v β y').val *ᵥ x) = x := by
    intro y' x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  have hne : ∀ (y' : LKCx.grp G β) (c : ℂ), (LKCx.toV G v β y').val *ᵥ z.1 = c • z.1 → c ≠ 0 := by
    rintro y' c hc rfl
    rw [zero_smul] at hc
    apply hz0
    rw [← hinvmul y' z.1, hc, Matrix.mulVec_zero]
  have inv : ∀ y' : LKCx.grp G β, LKCx.FixL G v β y' z.1 → LKCx.FixL G v β y'⁻¹ z.1 := by
    rintro y' ⟨c, hc⟩
    have hc0 := hne y' c hc
    have h1 : z.1 = c • ((LKCx.toV G v β y'⁻¹).val *ᵥ z.1) := by
      rw [← Matrix.mulVec_smul, ← hc, hinvmul]
    refine ⟨c⁻¹, ?_⟩
    calc (LKCx.toV G v β y'⁻¹).val *ᵥ z.1
        = c⁻¹ • (c • ((LKCx.toV G v β y'⁻¹).val *ᵥ z.1)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • z.1 := by rw [← h1]
  let zi : LKCx.PosV G v β := ⟨(LKCx.toV G v β y⁻¹).val *ᵥ z.1, herm_pos_toV_mulVec_of_pos G v β y⁻¹ z.1 z.2⟩
  let Q₂ : VQ D →+ Fin D.g → ℂ := Q.comp (actY L y).toAddMonoidHom
  have hQ₂ : ∀ w, Q₂ w = Q (actY L y w) := fun w => rfl
  have hback : ∀ w, Q₂ (actY L y⁻¹ w) = Q w := by
    intro w
    rw [hQ₂, actY_actY_inv]
  have hper : IsPerQ L β ρ Q₂ := (hA p D G L β y⁻¹).2.2.1 ρ Q Q₂ hQ hback
  have hrel₂ : RD.rel Q₂ zi.1 := RD.equiv y⁻¹ Q Q₂ z.1 hback hrel
  have key := RD.uniq Q Q₂ z zi hQ hper hrel hrel₂
  refine ⟨⟨fun hF => ?_, fun ⟨H, hH⟩ => ?_⟩, inv y⟩
  · obtain ⟨c, hc⟩ := inv y hF
    obtain ⟨h, hh⟩ := key.mpr ⟨c, hne _ c hc, hc⟩
    refine ⟨LinearMap.toMatrix' (h : (Fin D.g → ℂ) →ₗ[ℂ] Fin D.g → ℂ), fun w => ?_⟩
    rw [LinearMap.toMatrix'_mulVec, ← hQ₂, hh w]
    rfl
  · have hsurj : Function.Surjective (Matrix.toLin' H) := by
      rw [← LinearMap.range_eq_top]
      have hle : Submodule.span ℝ (Set.range ⇑Q) ≤ (LinearMap.range (Matrix.toLin' H)).restrictScalars ℝ := by
        rw [Submodule.span_le]
        rintro _ ⟨w, rfl⟩
        refine ⟨Q (actY L y⁻¹ w), ?_⟩
        rw [Matrix.toLin'_apply, ← hH, actY_actY_inv]
      rw [hQ.2.1] at hle
      exact eq_top_iff.mpr (fun x _ => hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ (Fin D.g → ℂ))))
    have hinj := LinearMap.injective_iff_surjective.mpr hsurj
    obtain ⟨c, hc0, hc⟩ := key.mp ⟨LinearEquiv.ofBijective (Matrix.toLin' H) ⟨hinj, hsurj⟩, fun w => by
      show Q₂ w = Matrix.toLin' H (Q w)
      rw [Matrix.toLin'_apply, hQ₂, hH]⟩
    have h2 := inv y⁻¹ ⟨c, hc⟩
    rwa [inv_inv] at h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRdAct
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem actOn_inC {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (c : G.C) (w : VQ D) :
    actOn L.rep (AfP p) (inC G (AfP p) c) ((1 : AfP p) ⊗ₜ w) = (1 : AfP p) ⊗ₜ (L.rep c w) := by
  simp only [actOn, inC, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  erw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, one_mul, Module.End.baseChangeHom, AlgHom.comp_apply]
  exact LinearMap.baseChange_tmul _ _ _

private theorem actG_toAf {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (B : GlobalTheory.LKCx.Form G)
    (y : GlobalTheory.LKCx.grp G B.β) (w : VQ D) :
    L.actG (B.toAf y) (actOn L.rep (AfP p) (trivX B : AfP p ⊗[ℚ] G.C) ((1 : AfP p) ⊗ₜ w)) =
      actOn L.rep (AfP p) (trivX B : AfP p ⊗[ℚ] G.C) ((1 : AfP p) ⊗ₜ (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) w)) := by
  have hval : (L.actG (B.toAf y) : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D))
      = actOn L.rep (AfP p) ((trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
          * (((trivX B)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := rfl
  rw [hval, ← Module.End.mul_apply, ← map_mul,
    show (trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
          * (((trivX B)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * (trivX B : AfP p ⊗[ℚ] G.C)
        = (trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) by
      simp [mul_assoc],
    map_mul, Module.End.mul_apply, actOn_inC]

theorem rdAct_of : RdAct := by
  intro p _ D G L B y h₁ h₂ w
  simp only [rd, actY]
  conv_rhs =>
    rw [← Module.End.mul_apply, ← map_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one, map_mul,
      Module.End.mul_apply, actG_toAf]

end UpperTheory.Gal.W2
end
end

