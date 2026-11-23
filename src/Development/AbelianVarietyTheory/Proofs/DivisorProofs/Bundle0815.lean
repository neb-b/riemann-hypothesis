module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemisimpleRingOfPosFormAdjointClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

theorem isSemisimpleRing_of_posForm_adjoint_closed :
    ∀ (r : ℕ) (Q : Matrix (Fin r) (Fin r) ℂ) (S : Subalgebra ℂ (Matrix (Fin r) (Fin r) ℂ)), Q.IsHermitian →
      (∀ z : Fin r → ℂ, z ≠ 0 → 0 < (star z ⬝ᵥ (Q *ᵥ z)).re) →
      (∀ x ∈ S, ∃ y ∈ S, Q * y = xᴴ * Q) → IsSemisimpleRing S := by
  intro r Q S hQ hpos hadj
  have hnd : ∀ w : Fin r → ℂ, star w ⬝ᵥ (Q *ᵥ w) = 0 → w = 0 := by
    intro w hw
    by_contra hne
    have := hpos w hne
    rw [hw] at this
    simp at this
  have key : ∀ (b : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ),
      star (b *ᵥ w) ⬝ᵥ (Q *ᵥ (b *ᵥ w)) = star w ⬝ᵥ ((bᴴ * Q * b) *ᵥ w) := by
    intro b w
    simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have step : ∀ b : Matrix (Fin r) (Fin r) ℂ, Q * b = bᴴ * Q →
      ∀ w : Fin r → ℂ, (b * b) *ᵥ w = 0 → b *ᵥ w = 0 := by
    intro b hb w hw
    apply hnd
    rw [key, show bᴴ * Q * b = Q * (b * b) by rw [← hb, Matrix.mul_assoc], ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_zero, dotProduct_zero]
  haveI : IsArtinianRing S := IsArtinianRing.of_finite ℂ _
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  obtain ⟨y, hyS, hy⟩ := hadj x.1 x.2
  let y' : S := ⟨y, hyS⟩
  have hyx : y' * x ∈ Ring.jacobson S := Ideal.mul_mem_left _ _ hx
  obtain ⟨n, hn⟩ : IsNilpotent (Ring.jacobson S) := IsSemiprimaryRing.isNilpotent
  have h1 : (y' * x) ^ n = 0 := by
    have := Ideal.pow_mem_pow hyx n
    rw [hn] at this
    simpa using this
  have h2 : (y * x.1) ^ n = 0 := by simpa [y'] using congrArg Subtype.val h1
  have hsa : Q * (y * x.1) = (y * x.1)ᴴ * Q := by
    have e1 : yᴴ * Q = Q * x.1 := by
      have := congrArg Matrix.conjTranspose hy
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ.eq,
        Matrix.conjTranspose_conjTranspose] at this
      exact this
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hy]
  have hz : ∀ m : ℕ, (y * x.1) ^ (m + 1) = 0 → y * x.1 = 0 := by
    intro m
    induction m with
    | zero => intro h; simpa using h
    | succ m ih =>
      intro hm
      apply ih
      rw [Matrix.ext_iff_mulVec]
      intro v
      have e2 : ((y * x.1) * (y * x.1)) *ᵥ ((y * x.1) ^ m *ᵥ v) = 0 := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, ← pow_succ', ← pow_succ', hm, Matrix.zero_mulVec]
      rw [Matrix.zero_mulVec, pow_succ', ← Matrix.mulVec_mulVec]
      exact step _ hsa _ e2
  have ha : y * x.1 = 0 := hz n (by rw [pow_succ, h2, zero_mul])
  apply Subtype.ext
  rw [Matrix.ext_iff_mulVec]
  intro w
  rw [ZeroMemClass.coe_zero, Matrix.zero_mulVec]
  apply hnd
  rw [key, ← hy, Matrix.mul_assoc, ha, Matrix.mul_zero, Matrix.zero_mulVec, dotProduct_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePrincMulUnit
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.ClassInv

theorem finPart_unit {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (hχ : IsValChar φ s κ 𝔣 Q χ)
    {u : (Af E)ˣ} (hu : u ∈ hatOUnits (condQ 𝔣 Q)) : finPart χ u = 1 := by
  refine OrderUnits.finPart_eq_one_of_level hχ.2.1 (fun v => ?_) hu
  by_cases hv : v ∈ Q
  · refine ⟨1, ?_, fun P hP => (hχ.2.2.2 v P hP).1 hv⟩
    rw [pow_one]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
  · exact ⟨expIn 𝔣 v, Dvd.dvd.mul_right (pow_multiplicity_dvd _ _) _,
      fun P hP => ((hχ.2.2.2 v P hP).2 hv _).2 le_rfl⟩

theorem lamInf_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E}
    (h : HasInfRatio χ φ fun i => (κ i : ℤ) + s) (α : Eˣ) :
    lamInf φ (2 * s) κ α =
      ((χ.inf α : ℂˣ) : ℂ) * (((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|) ^ s : ℝ) : ℂ) := by
  have hN : (((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|) ^ s : ℝ) : ℂ) = ∏ i, (φ i α * starRingEnd ℂ (φ i α)) ^ s := by
    rw [← TermUnit.prod_norm_sq hφ (α : E), ← Finset.prod_pow]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.mul_conj']
  rw [hN, (hasInfRatio_iff χ φ _).1 h α]
  unfold lamInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : φ i α ≠ 0 := by simp
  have h2 : starRingEnd ℂ (φ i α) ≠ 0 := by simp
  have h3 : ((κ i : ℤ) + s) = ((κ i + s : ℕ) : ℤ) := by push_cast; ring
  rw [h3, zpow_natCast, div_pow, inv_pow]
  field_simp
  ring

theorem lattice_princ_mul_unit {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} (y : (Af E)ˣ) (α : Eˣ)
    {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) :
    lattice c (Units.map (algebraMap E (Af E)).toMonoidHom α * y * u) = (fun x => (α : E) * x) '' lattice c y := by
  rw [lattice_mul_unit _ hu]
  ext x
  constructor
  · intro hx
    refine ⟨(α : E)⁻¹ * x, (mul_mem_lattice_princ c y α _).1 ?_, by simp⟩
    simpa using hx
  · rintro ⟨z, hz, rfl⟩
    exact (mul_mem_lattice_princ c y α z).2 hz

theorem classInvariance : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → (∀ (s : ℕ) (L : Set E), Homothety φ (2 * s) L) → ∀ s : ℕ, ClassInvariance φ s := by
  intro E _ _ _ I _ _ φ hφ hH s 𝔣 Q κ χ _ _ hχ y y' S S' hq hS hS'
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq)
  set a : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom α with ha
  have hy' : y' = a * y * u := by
    have : y' = y * (a * u) := by rw [hau]; group
    rw [this]; exact (by ac_rfl : y * (a * u) = a * y * u)
  subst hy'
  have hL := lattice_princ_mul_unit (c := condQ 𝔣 Q) y α hu
  rw [hL] at hS'
  have hS0 : S' 0 = (lamInf φ (2 * s) κ α)⁻¹ * S 0 := (hH s _ κ α S hS).2 S' hS'
  have hAB : ((finPart χ a : ℂˣ) : ℂ) * ((χ.inf α : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, show finPart χ a * χ.inf α = 1 from finPart_mul_inf χ α, Units.val_one]
  have hfu : finPart χ u = 1 := finPart_unit hχ hu
  have hmu : modF u = 1 := ObjModel.modF_unit hu
  have hma : modF a = (|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|)⁻¹ := IdeleModule.modF_princ α
  have hn : |((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| ≠ 0 := by
    have h0 : Algebra.norm ℚ (α : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 α.ne_zero
    exact abs_ne_zero.2 (by exact_mod_cast h0)
  have hmy : modF y ≠ 0 := (IdeleModule.modF_pos y).ne'
  rw [hS0, lamInf_eq hφ hχ.2.2.1 α]
  unfold lamFin
  rw [map_mul, map_mul, hfu, mul_one, IdeleModule.modF_mul, IdeleModule.modF_mul, hmu, mul_one, hma, Units.val_mul]
  have hF : ((finPart χ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA : ((finPart χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hB : ((χ.inf α : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA' : ((finPart χ a : ℂˣ) : ℂ) = (((χ.inf α : ℂˣ) : ℂ))⁻¹ := eq_inv_of_mul_eq_one_left hAB
  have hn' : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmy' : ((modF y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmy
  rw [hA']
  push_cast
  field_simp
  rw [div_pow]
  field_simp

end GlobalTheory.ClassInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfIsFrame
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBObs

theorem gm_id_res' {X : Scheme.{0}} {U V : X.Opens} (hle : V ≤ U) {x : X} (hx : x ∈ V) (a : Γ(X, U)ˣ) :
    gm (𝟙 X) x V (ReciprocityTheory.ChartRestriction.G.Semi.res hle a) = gm (𝟙 X) x U a :=
  gm_res (𝟙 X) x hle hx a

theorem lbIso_of_isFrame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (L L' : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → L.IsLB → L'.IsLB → IsFrame L V hV u → IsFrame L' V hV u → LBIso L L' := by
  intro X C _ V hV _ L L' u hB _ _ hF hF'
  obtain ⟨τ, hτg, hτ⟩ := hF
  obtain ⟨τ', hτ'g, hτ'⟩ := hF'

  have e : ∀ (T T' : C) (a : T ⟶ T') (m : L.ι) (x : X) (hx : x ∈ V T' ⊓ L.U m),
      gm (𝟙 X) x _ (τ T m) = gm (𝟙 X) x _ (u T T' a) * gm (𝟙 X) x _ (τ T' m) := by
    intro T T' a m x hx
    have h := congrArg (gm (𝟙 X) x (V T' ⊓ L.U m)) (hτ T T' a m)
    rwa [map_mul, gm_id_res' _ hx, gm_id_res' _ hx] at h
  have e' : ∀ (T T' : C) (a : T ⟶ T') (m : L'.ι) (x : X) (hx : x ∈ V T' ⊓ L'.U m),
      gm (𝟙 X) x _ (τ' T m) = gm (𝟙 X) x _ (u T T' a) * gm (𝟙 X) x _ (τ' T' m) := by
    intro T T' a m x hx
    have h := congrArg (gm (𝟙 X) x (V T' ⊓ L'.U m)) (hτ' T T' a m)
    rwa [map_mul, gm_id_res' _ hx, gm_id_res' _ hx] at h

  have key : ∀ (T₁ T₂ : C) (m : L.ι) (m' : L'.ι) (x : X), x ∈ V T₁ → x ∈ V T₂ → x ∈ L.U m → x ∈ L'.U m' →
      gm (𝟙 X) x (V T₁ ⊓ L'.U m') (τ' T₁ m') / gm (𝟙 X) x (V T₁ ⊓ L.U m) (τ T₁ m) =
        gm (𝟙 X) x (V T₂ ⊓ L'.U m') (τ' T₂ m') / gm (𝟙 X) x (V T₂ ⊓ L.U m) (τ T₂ m) := by
    intro T₁ T₂ m m' x h1 h2 hm hm'
    obtain ⟨T₃, ⟨a⟩, ⟨b⟩, h3, -⟩ := hB.2 T₁ T₂ x ⊤ trivial h1 h2
    rw [e T₁ T₃ a m x ⟨h3, hm⟩, e' T₁ T₃ a m' x ⟨h3, hm'⟩, e T₂ T₃ b m x ⟨h3, hm⟩, e' T₂ T₃ b m' x ⟨h3, hm'⟩,
      mul_div_mul_left_eq_div, mul_div_mul_left_eq_div]

  have hglue : ∀ p : L'.ι × L.ι, ∃ s : Γ(X, L'.U p.1 ⊓ L.U p.2)ˣ, ∀ (T : C) (x : X),
      x ∈ V T → x ∈ L'.U p.1 ⊓ L.U p.2 →
        gm (𝟙 X) x _ s = gm (𝟙 X) x (V T ⊓ L'.U p.1) (τ' T p.1) / gm (𝟙 X) x (V T ⊓ L.U p.2) (τ T p.2) := by
    intro p
    obtain ⟨s, hs⟩ := glue_unit (L'.U p.1 ⊓ L.U p.2) (fun T => V T ⊓ (L'.U p.1 ⊓ L.U p.2)) (fun T => inf_le_right)
      (fun x hx => by
        obtain ⟨T, hT, -⟩ := hB.1 x ⊤ trivial
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨T, hT, hx⟩)
      (fun T => ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf_left (V T) inf_le_left) (τ' T p.1) /
        ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf_left (V T) inf_le_right) (τ T p.2))
      (fun T₁ T₂ x hx => by
        simp only [map_div]
        rw [gm_id_res' _ hx.1, gm_id_res' _ hx.1, gm_id_res' _ hx.2, gm_id_res' _ hx.2]
        exact key T₁ T₂ p.2 p.1 x hx.1.1 hx.2.1 hx.1.2.2 hx.1.2.1)
    refine ⟨s, fun T x hT hx => ?_⟩
    have h := congrArg (gm (𝟙 X) x (V T ⊓ (L'.U p.1 ⊓ L.U p.2))) (hs T)
    simp only [map_div] at h
    have hTx : x ∈ V T ⊓ (L'.U p.1 ⊓ L.U p.2) := ⟨hT, hx⟩
    rwa [gm_id_res' _ hTx, gm_id_res' _ hTx, gm_id_res' _ hTx] at h
  choose w hw using hglue
  refine ⟨⟨w⟩, fun p q => ?_⟩
  apply ReciprocityTheory.ChartRestriction.G.Geo.Tor.unit_ext
  intro x hx
  obtain ⟨T, hT, -⟩ := hB.1 x ⊤ trivial
  have hp : x ∈ L'.U p.1 ⊓ L.U p.2 := hx.1
  have hq : x ∈ L'.U q.1 ⊓ L.U q.2 := hx.2

  have g1 := congrArg (gm (𝟙 X) x _) (hτ'g T p.1 q.1)
  have g2 := congrArg (gm (𝟙 X) x _) (hτg T p.2 q.2)
  have hx1 : x ∈ V T ⊓ L'.U p.1 ⊓ L'.U q.1 := ⟨⟨hT, hp.1⟩, hq.1⟩
  have hx2 : x ∈ V T ⊓ L.U p.2 ⊓ L.U q.2 := ⟨⟨hT, hp.2⟩, hq.2⟩
  rw [map_mul, gm_id_res' _ hx1, gm_id_res' _ hx1, gm_id_res' _ hx1] at g1
  rw [map_mul, gm_id_res' _ hx2, gm_id_res' _ hx2, gm_id_res' _ hx2] at g2
  have hwp : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q)
      (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_left : (L'.div L).U p ⊓ (L'.div L).U q ≤ (L'.div L).U p) (w p)) =
      gm (𝟙 X) x ((L'.div L).U p) (w p) := gm_id_res' _ hx _
  have hwq : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q)
      (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_right : (L'.div L).U p ⊓ (L'.div L).U q ≤ (L'.div L).U q) (w q)) =
      gm (𝟙 X) x ((L'.div L).U q) (w q) := gm_id_res' _ hx _
  have hx' : x ∈ L'.U p.1 ⊓ L.U p.2 ⊓ (L'.U q.1 ⊓ L.U q.2) := hx
  have hg : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q) ((L'.div L).g p q) =
      gm (𝟙 X) x (L'.U p.1 ⊓ L'.U q.1) (L'.g p.1 q.1) * (gm (𝟙 X) x (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := by
    show gm (𝟙 X) x (L'.U p.1 ⊓ L.U p.2 ⊓ (L'.U q.1 ⊓ L.U q.2))
      (ReciprocityTheory.ChartRestriction.G.Semi.res _ (L'.g p.1 q.1) * (ReciprocityTheory.ChartRestriction.G.Semi.res _ (L.g p.2 q.2))⁻¹) = _
    rw [map_mul, map_inv, gm_id_res' _ hx', gm_id_res' _ hx']
  rw [map_mul, hwp, hwq, hg]
  erw [hw p T x hT hp, hw q T x hT hq]
  rw [g1, g2]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

end GlobalTheory.LBObs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfCountableHolomorphicImagesCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

theorem dimH_image_le_of_differentiableOn_complex {d d' : ℕ} {U : Set (Fin d → ℂ)}
    {f : (Fin d → ℂ) → (Fin d' → ℂ)} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    dimH (f '' U) ≤ (Module.finrank ℝ (Fin d → ℂ) : ENNReal) := by
  set S : ℕ → Set (Fin d → ℂ) := fun n =>
    {x | ∀ y, dist y x < 1 / ((n : ℝ) + 1) → dist (f y) (f x) ≤ ((n : ℝ) + 1) * dist y x}
    with hS
  have hcov : f '' U ⊆ ⋃ n, f '' S n := by
    rintro _ ⟨x, hx, rfl⟩
    have hd : DifferentiableAt ℂ f x := (hf x hx).differentiableAt (hU.mem_nhds hx)
    obtain ⟨C, hC, hCw⟩ := hd.hasFDerivAt.isBigO_sub.exists_pos
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hCw.bound
    obtain ⟨n, hn⟩ := exists_nat_gt (max C (1 / ε))
    refine Set.mem_iUnion.2 ⟨n, x, ?_, rfl⟩
    intro y hy
    have hn1 : C < (n : ℝ) + 1 := by linarith [le_max_left C (1 / ε)]
    have hn2 : 1 / ε < (n : ℝ) + 1 := by linarith [le_max_right C (1 / ε)]
    have hy' : dist y x < ε := by
      refine lt_of_lt_of_le hy ?_
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hn2
      linarith
    have := hεb hy'
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖f y - f x‖ ≤ C * ‖y - x‖ := this
      _ ≤ ((n : ℝ) + 1) * ‖y - x‖ := by gcongr
  have hSn : ∀ n, dimH (f '' S n) ≤ dimH (S n) := by
    intro n
    apply dimH_image_le_of_locally_lipschitzOn
    intro x _
    refine ⟨((n : NNReal) + 1), S n ∩ Metric.ball x (1 / (2 * ((n : ℝ) + 1))),
      inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ (by positivity)), ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have hab : dist a b < 1 / ((n : ℝ) + 1) := by
      have h1 := Metric.mem_ball.1 ha.2
      have h2 := Metric.mem_ball'.1 hb.2
      calc dist a b ≤ dist a x + dist x b := dist_triangle _ _ _
        _ < 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) := add_lt_add h1 h2
        _ = 1 / ((n : ℝ) + 1) := by field_simp; ring
    have := hb.1 a hab
    simpa using this
  calc dimH (f '' U) ≤ dimH (⋃ n, f '' S n) := dimH_mono hcov
    _ = ⨆ n, dimH (f '' S n) := dimH_iUnion _
    _ ≤ dimH (Set.univ : Set (Fin d → ℂ)) :=
        iSup_le fun n => (hSn n).trans (dimH_mono (Set.subset_univ _))
    _ = _ := Real.dimH_univ_eq_finrank _

theorem le_of_countable_holomorphic_images_cover :
    ∀ (d d' : ℕ) (K : Type) [Countable K] (U : K → Set (Fin d → ℂ))
      (f : K → (Fin d → ℂ) → (Fin d' → ℂ)) (W : Set (Fin d' → ℂ)),
      (∀ i, IsOpen (U i)) → (∀ i, DifferentiableOn ℂ (f i) (U i)) → IsOpen W →
      W.Nonempty → W ⊆ ⋃ i, f i '' U i → d' ≤ d := by
  intro d d' K _ U f W hU hf hW hne hcov
  obtain ⟨w, hw⟩ := hne
  have h1 : dimH W = (Module.finrank ℝ (Fin d' → ℂ) : ENNReal) :=
    Real.dimH_of_mem_nhds (hW.mem_nhds hw)
  have h2 : dimH W ≤ (Module.finrank ℝ (Fin d → ℂ) : ENNReal) := by
    calc dimH W ≤ dimH (⋃ i, f i '' U i) := dimH_mono hcov
      _ = ⨆ i, dimH (f i '' U i) := dimH_iUnion _
      _ ≤ _ := iSup_le fun i => dimH_image_le_of_differentiableOn_complex (hU i) (hf i)
  rw [h1] at h2
  have h3 : Module.finrank ℝ (Fin d' → ℂ) ≤ Module.finrank ℝ (Fin d → ℂ) := by
    exact_mod_cast h2
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at h3
  simp at h3
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfInjOnDifferentiableOnComplex
section
open Set

namespace GlobalTheory.InjHol

def padZero (m n : ℕ) : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun i => if h : (i : ℕ) < m then LinearMap.proj ⟨i, h⟩ else 0

theorem padZero_apply_of_lt {m n : ℕ} (y : Fin m → ℂ) (i : Fin n) (h : (i : ℕ) < m) :
    padZero m n y i = y ⟨i, h⟩ := by
  simp [padZero, h]

theorem padZero_injective {m n : ℕ} (hmn : m ≤ n) : Function.Injective (padZero m n) := by
  intro y z hyz
  funext j
  have := congrFun hyz ⟨j, lt_of_lt_of_le j.isLt hmn⟩
  rwa [padZero_apply_of_lt (n := n) y ⟨j, _⟩ j.isLt, padZero_apply_of_lt (n := n) z ⟨j, _⟩ j.isLt] at this

theorem le_of_injOn_differentiableOn :
    ∀ (d d' : ℕ) (U : Set (Fin d → ℂ)) (f : (Fin d → ℂ) → (Fin d' → ℂ)), IsOpen U →
      U.Nonempty → DifferentiableOn ℂ f U → Set.InjOn f U → d ≤ d' := by
  intro d d' U f hU hne hf hinj
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, ha⟩ := hne
  let L : (Fin d' → ℂ) →L[ℂ] (Fin d → ℂ) := LinearMap.toContinuousLinearMap (padZero d' d)
  have hL : Function.Injective L := padZero_injective hlt.le
  have hg : DifferentiableOn ℂ (fun x => L (f x)) U :=
    L.differentiable.comp_differentiableOn hf
  have hgi : Set.InjOn (fun x => L (f x)) U := fun x hx y hy hxy => hinj hx hy (hL hxy)
  have hb := bijective_fderiv_of_injOn d U (fun x => L (f x)) hU hg hgi a ha
  have hfa : DifferentiableAt ℂ f a := hf.differentiableAt (hU.mem_nhds ha)
  have hder : fderiv ℂ (fun x => L (f x)) a = L.comp (fderiv ℂ f a) :=
    (L.hasFDerivAt.comp a hfa.hasFDerivAt).fderiv
  rw [hder, ContinuousLinearMap.coe_comp'] at hb
  have hsurj : Function.Surjective (padZero d' d) := Function.Surjective.of_comp hb.2
  have hr := LinearMap.finrank_range_le (padZero d' d)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at hr
  omega

end GlobalTheory.InjHol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterConjugate
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.LevelCharacterConjugate

theorem levPOf_inv {D : D7} {G K : Type} [Group G] [Field K] {Pg : Finset (Pl D.host.E)} {r : ℕ}
    (eG : G ≃* G0 Pg r) (σ : K →+* ℂ) (P : Subgroup G) (ψ : P →* Kˣ) :
    levPOf eG σ P ψ⁻¹ = (levPOf eG σ P ψ).conj := by
  have hc : (Units.map (σ : K →* ℂ)).comp (ψ⁻¹.comp (eG.symm.toMonoidHom.subgroupComap P)) =
      ((Units.map (σ : K →* ℂ)).comp (ψ.comp (eG.symm.toMonoidHom.subgroupComap P)))⁻¹ :=
    MonoidHom.ext fun x => by simp only [MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv]
  exact congrArg (LevelP.mk (Subgroup.comap eG.symm.toMonoidHom P)) hc

theorem liftLevel_fixedEmbedding_eq_conj_rowLevel {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool)
    (h : A.v0 = InfinitePlace.mk D.what₂.embLL) : R.levL F b (sg0 D A) = (R.levR F b).conj := by
  rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ h]
  exact levPOf_inv _ _ _ _

end GlobalTheory.Proof.LevelCharacterConjugate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankSimultaneousEigenSubmoduleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieMult_iff_finrank_simultaneousEigenSubmodule : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G]
  (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (k : Type) [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (m : ℕ),
    Module.Finite k (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM t G) →
      (LieMult act t τ m ↔ Module.finrank k (eigSub (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := t) (S := k) act) τ) = m) := by
  first | exact @GlobalTheory.UPel.HT.LieLin.lieMult_iff_finrank | exact GlobalTheory.UPel.HT.LieLin.lieMult_iff_finrank | (intros; apply GlobalTheory.UPel.HT.LieLin.lieMult_iff_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlong
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

def LiftsAlong {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {U : Over (Sp R)} (M : LB (A ⊗ U).left)
    (B : Type) [CommRing B] (I : Ideal B) : Prop :=
  ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left)
    (u₀ : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ U),
    Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y) (by simp) :
      Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ T) u₀ →
    ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemRangeNormStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_mem_range_norm_of_not_mem : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (x y : Fˣ), x ∉ (Units.map (Algebra.norm F : E →* F)).range → y ∉ (Units.map (Algebra.norm F : E →* F)).range → x * y ∈ (Units.map (Algebra.norm F : E →* F)).range := by
  first | exact @GlobalTheory.KSp.NormIndex.mul_mem_range_norm | exact GlobalTheory.KSp.NormIndex.mul_mem_range_norm | (intros; apply GlobalTheory.KSp.NormIndex.mul_mem_range_norm <;> assumption)
end

