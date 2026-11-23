module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.StarInvMulVecDotProductMulVecInvMulVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadings
section
set_option autoImplicit false

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

namespace GlobalTheory.Unframe

theorem lUnif_moveR {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G) (hw : ∀ i σ, w i σ ∈ Subgroup.center G) (hU : R.LUnif) :
    (moveR R w).LUnif := by
  intro i σ
  obtain ⟨h1, h2, h3⟩ := hU i σ
  have hl : ∀ x, (R.FW i).ρ (w i σ)⁻¹ ((R.FW i).ρ (w i σ) x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hr : ∀ x, (R.FW i).ρ (w i σ) ((R.FW i).ρ (w i σ)⁻¹ x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hc : ∀ g x, (R.FW i).ρ (w i σ) ((R.FW i).ρ g x) = (R.FW i).ρ g ((R.FW i).ρ (w i σ) x) := fun g x => by
    rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.mem_center_iff.1 (hw i σ) g, map_mul, Module.End.mul_apply]
  refine ⟨fun n b hb => ?_, ?_, fun g x => ?_⟩
  · have hinj : Function.Injective ((R.FW i).ρ (w i σ)) := Function.LeftInverse.injective hl
    exact h1 n (fun k => (R.FW i).ρ (w i σ) (b k)) (hb.map' _ (LinearMap.ker_eq_bot.2 hinj))
  · refine top_le_iff.1 (h2 ▸ Submodule.span_mono ?_)
    rintro _ ⟨x, rfl⟩
    exact ⟨(R.FW i).ρ (w i σ)⁻¹ x, congrArg ((R.FW i).j σ) (hr x)⟩
  · have h := h3 g ((R.FW i).ρ (w i σ) x)
    rw [← hc] at h
    exact h

end GlobalTheory.Unframe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFibreFrameAtOriginEqRigidification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.RigAtOrigin

theorem frame_at_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left) (he : eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A)
    (w : LB.Iso x.P.L (D.P.L.pull φ)), w.IsGen →
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) he D.P.L D.rig) →
    ∀ (g : ℕ) (u : HolUnif x.P.A x.P.L g), u.IsRig x.rig → ∀ (k : x.P.L.ι) (j : D.P.L.ι),
      ⊤ ≤ (u.ex 0).left ⁻¹ᵁ x.P.L.U k → ⊤ ≤ (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A) ⁻¹ᵁ D.P.L.U j →
      valAt' (u.ex 0).left _ (w.s (fun _ => j, k)).val * u.fr k 0 =
        valF (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => j)) (D.rig.s (fun _ => j)).val := by
  intro R _ _ _ D x φ he w _ hM g u hrig k j hk hj
  have hu0 : (u.ex 0).left = eSec x.P.A := by
    rw [(u.ker 0).2 u.Λ.zero_mem]
    change (toUnit _ ≫ η[x.P.A]).left = η[x.P.A].left
    rw [toUnit_unit, Category.id_comp]
  have hj' : ⊤ ≤ (𝟙 (Sp ℂ) ≫ eSec x.P.A ≫ φ) ⁻¹ᵁ D.P.L.U j := by
    rw [Category.id_comp, he]; exact hj
  have hk' : ⊤ ≤ (𝟙 (Sp ℂ) ≫ eSec x.P.A) ⁻¹ᵁ x.P.L.U k := by
    rw [Category.id_comp, ← hu0]; exact hk
  have e := GlobalTheory.ArcThetaFib.maps_val' φ _ he D.P.L D.rig x.P.L w x.rig hM (𝟙 (Sp ℂ)) j k hj' hk'
  have hr := hrig (fun _ => k) (fun q hq => Set.mem_iInter.2 fun _ => hk' hq)
  rw [hu0, hr]
  simp only [Category.id_comp] at e
  exact e.symm

end GlobalTheory.RigAtOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringFractionsOfEssFiniteTypeComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem valuationSubring_fractions_of_essFiniteType : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (hψ : ∀ a, ψ a ∈ V), (ψ.codRestrict V hψ).EssFiniteType → ∃ s₀ : Finset L, (∀ x ∈ s₀, x ∈ V) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  classical
  intro L _ ψ V hψ h
  letI : Algebra ℂ V := (ψ.codRestrict V hψ).toAlgebra
  have h' : Algebra.EssFiniteType ℂ V := h
  obtain ⟨s, hs⟩ := h'.cond
  refine ⟨s.image (fun x : V => (x : L)), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have key : ∀ x ∈ Algebra.adjoin ℂ (s : Set V),
      ((x : V) : L) ∈ Subring.closure (Set.range ψ ∪ ↑(s.image (fun x : V => (x : L)))) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Subring.subset_closure
      right
      rw [Finset.coe_image]
      exact ⟨x, hx, rfl⟩
    | algebraMap r =>
      apply Subring.subset_closure
      left
      exact ⟨r, rfl⟩
    | add x y _ _ hx hy =>
      simpa using Subring.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      simpa using Subring.mul_mem _ hx hy
  intro v hv
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj
    (Submonoid.comap (algebraMap (↥(Algebra.adjoin ℂ (s : Set V))) V) (IsUnit.submonoid V)) (⟨v, hv⟩ : V)
  have hu : IsUnit ((m : Algebra.adjoin ℂ (s : Set V)) : V) := m.2
  obtain ⟨u, hu'⟩ := hu
  have hinv : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) * (((u⁻¹ : Vˣ) : V) : L) = 1 := by
    rw [← hu']
    change (((u : V) * ((u⁻¹ : Vˣ) : V) : V) : L) = ((1 : V) : L)
    rw [u.mul_inv]
  have hd0 : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have hmL := congrArg (fun z : V => (z : L)) hm
  simp only at hmL
  refine ⟨((a : V) : L), key _ a.2, (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L),
    key _ (m : Algebra.adjoin ℂ (s : Set V)).2, hd0, ?_, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((u⁻¹ : Vˣ) : V).2
  · rw [eq_div_iff hd0]
    simpa using hmL

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonal
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.QWDom

open Matrix in
theorem exists_pos_posSemidef_sub_smul_one {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (A - c • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ hA.1.eigenvalues i := by
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ hA.1.eigenvalues Finset.univ_nonempty
      exact ⟨_, hA.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ _)⟩
  refine ⟨c, hc, ?_⟩
  have hs := hA.1.spectral_theorem
  have h1 : c • (1 : Matrix n n ℝ) = Unitary.conjStarAlgAut ℝ _ hA.1.eigenvectorUnitary (c • 1) := by
    rw [map_smul, map_one]
  rw [h1]
  conv => arg 1; arg 1; rw [hs]
  rw [← map_sub, Unitary.conjStarAlgAut_apply]
  rw [Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff]
  rw [smul_one_eq_diagonal, diagonal_sub]
  exact PosSemidef.diagonal fun i => by simpa using hle i

open Matrix in
theorem gram_nonneg_int {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y)
    (y : Fin s → X) (z : Fin s → ℤ) : 0 ≤ ∑ u, ∑ v, z u * β (y u) (y v) * z v := by
  have h := hβ (∑ u, z u • y u)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
  have e : ∑ u, ∑ v, z u * β (y u) (y v) * z v = ∑ x, z x * ∑ x1, z x1 * β (y x1) (y x) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [e]; exact h

open Matrix in
theorem gram_nonneg_rat {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y)
    (y : Fin s → X) (q : Fin s → ℚ) :
    0 ≤ ∑ u, ∑ v, (q u : ℝ) * (β (y u) (y v) : ℝ) * (q v : ℝ) := by
  set D : ℕ := ∏ u, (q u).den with hD
  have hDpos : (0 : ℝ) < D := by
    have : 0 < D := Finset.prod_pos fun u _ => (q u).den_pos
    exact_mod_cast this
  have hz : ∀ u, ∃ z : ℤ, (q u : ℝ) * D = z := by
    intro u
    obtain ⟨k, hk⟩ : (q u).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ u)
    refine ⟨(q u).num * k, ?_⟩
    rw [hk]
    have hq : (q u : ℝ) = (q u).num / (q u).den := by exact_mod_cast (Rat.num_div_den (q u)).symm
    have hd : ((q u).den : ℝ) ≠ 0 := by exact_mod_cast (q u).den_nz
    rw [hq]; push_cast; field_simp
  choose z hz using hz
  have h0 : (0 : ℝ) ≤ ∑ u, ∑ v, (z u : ℝ) * (β (y u) (y v) : ℝ) * (z v : ℝ) := by
    exact_mod_cast gram_nonneg_int β hβ y z
  have : ∑ u, ∑ v, (z u : ℝ) * (β (y u) (y v) : ℝ) * (z v : ℝ) =
      (D : ℝ) ^ 2 * ∑ u, ∑ v, (q u : ℝ) * (β (y u) (y v) : ℝ) * (q v : ℝ) := by
    simp only [← hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [this] at h0
  exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h0

open Matrix in
theorem gram_posSemidef {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hsym : ∀ a b, β a b = β b a) (hβ : ∀ y, 0 ≤ β y y) (y : Fin s → X) :
    (Matrix.of fun u v => (β (y u) (y v) : ℝ)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext u v
    simp [conjTranspose_apply, hsym (y u) (y v)]
  · have hcl : IsClosed {x : Fin s → ℝ | 0 ≤ ∑ u, ∑ v, x u * (β (y u) (y v) : ℝ) * x v} :=
      isClosed_le continuous_const (by fun_prop)
    have hx : 0 ≤ ∑ u, ∑ v, x u * (β (y u) (y v) : ℝ) * x v :=
      (DenseRange.piMap fun _ => Rat.denseRange_cast (𝕜 := ℝ)).induction_on x hcl
        fun q => gram_nonneg_rat β hβ y q
    simp only [star_trivial, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
    refine le_of_le_of_eq hx (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_)
    ring

open Matrix in
theorem qW_ge : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ y : Fin s → X, c * (∑ u, β (y u) (y u) : ℤ) ≤ (qW W β y : ℤ) := by
  intro s W hW
  obtain ⟨c, hc, hP⟩ := exists_pos_posSemidef_sub_smul_one hW
  refine ⟨c / 2, by positivity, fun X _ β hsym hβ y => ?_⟩
  have hM := gram_posSemidef β hsym hβ y
  have ht := GlobalTheory.trace_mul_nonneg_of_posSemidef hP hM
  rw [Matrix.sub_mul, trace_sub, Matrix.smul_mul, Matrix.one_mul, trace_smul, sub_nonneg] at ht
  simp only [trace, diag, Matrix.mul_apply, Matrix.map_apply, Matrix.add_apply, transpose_apply, Matrix.of_apply,
    smul_eq_mul] at ht
  have e : ∑ u, ∑ v, ((W u v + W v u : ℤ) : ℝ) * (β (y v) (y u) : ℝ) = 2 * (qW W β y : ℝ) := by
    simp only [qW, Int.cast_sum, Int.cast_mul, Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [two_mul]
    congr 1
    · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [hsym]
    · rw [Finset.sum_comm]
  push_cast at ht e ⊢
  linarith

end GlobalTheory.Poinc.QWDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDegenerationTorsionClassical
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl.WpK

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

theorem ex_zero : d.ex 0 = 1 := by
  have h := d.ex_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem ex_nsmul (i : ℕ) (z : Fin g' → ℂ) : d.ex (i • z) = d.ex z ^ i := by
  induction i with
  | zero => rw [zero_smul, pow_zero, ex_zero]
  | succ i ih => rw [succ_nsmul, d.ex_add, ih, pow_succ]

theorem cubN_frame (k : ℕ) (x' x : Fin g' → ℂ) :
    cubN N.θ k 1 (d.ex x') (d.ex x) * d.fr (k • x') * d.fr x * d.fr (x' + x) ^ k =
      d.fr (k • x' + x) * (d.fr x' * d.fr x) ^ k := by
  induction k with
  | zero => simp [cubN, d.fr_zero]
  | succ k ih =>
    have h := d.cub (k • x') x' x
    rw [ex_nsmul] at h
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, succ_nsmul, _root_.one_mul (d.ex x' ^ k)]
    replace h := congrArg Additive.ofMul h
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [pow_succ, ofMul_mul] at h ih ⊢
    linear_combination (norm := abel) h + ih

theorem full_transpose : (d.full σ 0)ᵀ = d.full σ 0 := by
  simp [CD.full, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, d.symm.eq, d.toricPeriodBlock_isSymm.eq]

theorem dot_split' (u v : Fin g → ℂ) : u ⬝ᵥ v = zP σ u ⬝ᵥ zP σ v + tP σ u ⬝ᵥ tP σ v := by
  simp only [dotProduct, zP, tP]
  rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]

end GlobalTheory.MBLow.Cl.WpK
end

noncomputable section
namespace GlobalTheory.MBLow.Cl.WpK
variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

theorem tk_frame {k : ℕ} (hk : 0 < k) {M Nn M' Nn' : Fin g → ℤ} {p p' : N.QT k} (h : d.Rep σ k M Nn p)
    (h' : d.Rep σ k M' Nn' p') :
    (N.tk p p' : ℂ) * (d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn') + zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)) : ℂ) ^ k =
      Complex.exp (2 * Real.pi * Complex.I * (cv Nn' ⬝ᵥ (k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)) *
        ((d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn')) : ℂ) * d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn))) ^ k := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  set Z := (k : ℂ)⁻¹ • perV (d.full σ 0) M Nn with hZ
  set Z' := (k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn' with hZ'
  set z := zP σ Z
  set z' := zP σ Z'
  set y' := p'.1.1.toAdd with hy'
  have hco : co bX y' = cv (tP σ Nn') := by rw [hy', h'.1]; exact Exp.co_sum _
  set cy := d.t12 *ᵥ co bX y' with hcy
  set per' := perV d.τ (zP σ M') (zP σ Nn') with hper
  have e : k • z' = cy + per' := by
    have : k • z' = zP σ (perV (d.full σ 0) M' Nn') := by
      funext i
      simp only [z', Z', zP, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
      rw [← _root_.mul_assoc, mul_inv_cancel₀ hk', _root_.one_mul]
    rw [this, Exp.leftComponent_periodVector, hcy, hco, add_comm]
  have e2 : k • z' + z = (cy + z) + per' := by rw [e]; abel
  have c := congrArg (Units.val : ℂˣ → ℂ) (cubN_frame d k z' z)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c
  rw [e2] at c
  have s := h.2.2 y'
  have f1 := Exp.fr_shift d (zP σ M') (zP σ Nn') (cy + z)
  have f2 := Exp.fr_shift d (zP σ M') (zP σ Nn') cy
  rw [e] at c
  rw [dotProduct_add, Exp.exp_two_pi_add] at f1
  have hT : cv Nn' ⬝ᵥ Z = cv (zP σ Nn') ⬝ᵥ z + co bX y' ⬝ᵥ tP σ Z := by
    rw [dot_split' σ, hco]; rfl
  rw [hT, Exp.exp_two_pi_add, NumD.tk, h.2.1, h'.2.1, Units.val_mul]
  set E1 := Complex.exp (2 * Real.pi * Complex.I * (co bX y' ⬝ᵥ tP σ Z))
  set E2 := Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn') ⬝ᵥ z))
  set E3 := Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn') ⬝ᵥ cy))
  have nA := (d.fr (cy + z)).ne_zero
  have nB := (d.fr (cy + per')).ne_zero
  have nC := (d.fr z).ne_zero
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero nA nB) nC)
  linear_combination (((cubN N.θ k 1 (d.ex z') (d.ex z) : ℂˣ) : ℂ) * d.fr (cy + per') * d.fr z * (d.fr (z' + z) : ℂ) ^ k) * s +
    (E1 * d.fr cy * d.fr z) * c + (E1 * d.fr cy * d.fr z * ((d.fr z' : ℂ) * d.fr z) ^ k) * f1 -
    (E2 * E1 * ((d.fr z' : ℂ) * d.fr z) ^ k * d.fr (cy + z) * d.fr z) * f2

end GlobalTheory.MBLow.Cl.WpK
end

namespace GlobalTheory.MBLow.Cl

theorem wp_classical : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ k : ℕ, 0 < k → ∀ M Nn M' Nn' p p', d.Rep σ k M Nn p →
    d.Rep σ k M' Nn' p' → (N.wp p p' : ℂ) =
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv M ⬝ᵥ cv Nn' - cv Nn ⬝ᵥ cv M') / k) := by
  intro N g' r g bX d σ k hk M Nn M' Nn' p p' h h'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have a := WpK.tk_frame d σ hk h h'
  have b := WpK.tk_frame d σ hk h' h
  rw [add_comm, mul_comm (d.fr _ : ℂ)] at b
  have n1 := pow_ne_zero k (d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn') +
    zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn))).ne_zero
  have hs : cv Nn' ⬝ᵥ d.full σ 0 *ᵥ cv Nn = cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn' := by
    rw [Exp.dotProduct_mulVec_eq_transpose_mulVec, WpK.full_transpose]
  have key : Complex.exp (2 * Real.pi * Complex.I * (cv Nn' ⬝ᵥ (k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)) =
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv M ⬝ᵥ cv Nn' - cv Nn ⬝ᵥ cv M') / k) *
      Complex.exp (2 * Real.pi * Complex.I * (cv Nn ⬝ᵥ (k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn')) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [perV, dotProduct_smul, dotProduct_add, smul_eq_mul]
    rw [hs, dotProduct_comm (cv M) (cv Nn')]
    field_simp
    ring
  rw [NumD.wp, Units.val_div_eq_div_val, div_eq_iff (N.tk p' p).ne_zero]
  apply mul_right_cancel₀ n1
  rw [a, key, _root_.mul_assoc _ (N.tk p' p : ℂ), b, _root_.mul_assoc]

end GlobalTheory.MBLow.Cl
end

