module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0545
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DiscreteTopologySpanOfLinearIndependent
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianDualPairInCoisotropic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Module

theorem exists_lagrangian_dual_in_coisotropic : ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), Mᵀ = -M → M.det ≠ 0 → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → ∃ (d : ℕ) (e f : Fin d → Fin r → ℝ), (∀ i, e i ∈ W) ∧ (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) ∧ (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) ∧ Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ := by
  classical
  intro r M W hskew hdet hW
  set B : LinearMap.BilinForm ℝ (Fin r → ℝ) := Matrix.toBilin' M with hBdef
  have hB : ∀ v w, B v w = v ⬝ᵥ M *ᵥ w := fun v w => by
    simp [hBdef, Matrix.toBilin'_apply']
  have hskewB : ∀ v w, B v w = - B w v := by
    intro v w
    rw [hB, hB, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hskew, Matrix.neg_mulVec,
      neg_dotProduct, dotProduct_comm]
  have hBalt : ∀ v, B v v = 0 := fun v => by have := hskewB v v; linarith
  have hrefl : B.IsRefl := fun x y h => by rw [hskewB, h, neg_zero]
  have hnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M hdet
  let P : ℕ → Prop := fun n => ∃ L : Submodule ℝ (Fin r → ℝ), L ≤ W ∧
    (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ finrank ℝ L = n
  have P0 : P 0 := ⟨⊥, bot_le, by simp, finrank_bot ℝ _⟩
  obtain ⟨L, hLW, hLiso, hLdim⟩ : P (Nat.findGreatest P r) := Nat.findGreatest_spec (Nat.zero_le _) P0
  have hmax : ∀ v ∈ W, (∀ l ∈ L, B v l = 0) → v ∈ L := by
    intro v hvW hvL
    by_contra hv
    have hlt : L < L ⊔ Submodule.span ℝ {v} := lt_of_le_of_ne le_sup_left (fun h => hv (by
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    have hiso : ∀ x ∈ L ⊔ Submodule.span ℝ {v}, ∀ y ∈ L ⊔ Submodule.span ℝ {v}, B x y = 0 := by
      intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hb'
      have h1 := hLiso a ha a' ha'
      have h2 := hvL a' ha'
      have h3 : B a v = 0 := by rw [hskewB, hvL a ha, neg_zero]
      have h4 := hBalt v
      simp [map_add (f := _), map_smul, h1, h2, h3, h4]
    have hle : L ⊔ Submodule.span ℝ {v} ≤ W :=
      sup_le hLW (by rw [Submodule.span_le]; simpa using hvW)
    have hP : P (finrank ℝ ↥(L ⊔ Submodule.span ℝ {v})) := ⟨_, hle, hiso, rfl⟩
    have h5 := Nat.le_findGreatest (by simpa using Submodule.finrank_le (L ⊔ Submodule.span ℝ {v})) hP
    have h6 := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hWo : B.orthogonal W ≤ L := by
    intro x hx
    have hxW : x ∈ W := hW x (fun w hw => by rw [← hB, hskewB, hx w hw, neg_zero])
    exact hmax x hxW (fun l hl => by rw [hskewB, hx l (hLW hl), neg_zero])
  let b := Module.finBasis ℝ L
  let e : Fin (finrank ℝ L) → Fin r → ℝ := fun i => ((b i : L) : Fin r → ℝ)
  have heL : ∀ i, e i ∈ L := fun i => (b i).2
  have hext : ∀ (φ : (Fin r → ℝ) →ₗ[ℝ] ℝ), (∀ j, φ (e j) = 0) → ∀ l ∈ L, φ l = 0 := by
    intro φ hφ l hl
    have : φ ∘ₗ L.subtype = 0 := b.ext (fun j => by simpa using hφ j)
    simpa using LinearMap.congr_fun this ⟨l, hl⟩
  let φ : (Fin r → ℝ) →ₗ[ℝ] (Fin (finrank ℝ L) → ℝ) := LinearMap.pi (fun j => B.flip (e j))
  have hφ : ∀ v j, φ v j = B v (e j) := fun v j => rfl
  have hker : LinearMap.ker φ = B.orthogonal L := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h l hl
      have h' := hext (B v) (fun j => by rw [← hφ, h]; rfl) l hl
      rw [hskewB, h', neg_zero]
    · intro h
      funext j
      rw [Pi.zero_apply, hφ, hskewB, h _ (heL j), neg_zero]
  have hrange : LinearMap.range φ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hker, LinearMap.BilinForm.finrank_orthogonal hnd] at h1
    have h2 : finrank ℝ L ≤ r := by simpa using Submodule.finrank_le L
    simp only [Module.finrank_fin_fun] at h1 ⊢
    omega
  have hsurj : ∀ y, ∃ x, φ x = y := fun y => by
    have : y ∈ LinearMap.range φ := by rw [hrange]; trivial
    exact this
  choose f hf using fun i : Fin (finrank ℝ L) => hsurj (Pi.single i 1)
  have hfe : ∀ i j, B (f i) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hφ, hf i, Pi.single_apply]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · simp [h, Ne.symm h]
  refine ⟨finrank ℝ L, e, f, fun i => hLW (heL i),
    fun i j => by rw [← hB]; exact hLiso _ (heL i) _ (heL j),
    fun i j => by rw [← hB]; exact hfe i j, ?_⟩
  set U := Submodule.span ℝ (Set.range (Sum.elim e f)) with hU
  have hUo : B.orthogonal U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hve : ∀ j, B (e j) v = 0 := fun j => hv _ (Submodule.subset_span ⟨Sum.inl j, rfl⟩)
    have hvf : ∀ i, B (f i) v = 0 := fun i => hv _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
    have hvL : ∀ l ∈ L, B v l = 0 := hext (B v) (fun j => by rw [hskewB, hve j, neg_zero])
    have hvW : v ∈ W := by
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W]
      intro x hx
      rw [hskewB, hvL x (hWo hx), neg_zero]
    have hvL' : v ∈ L := hmax v hvW hvL
    have hv' : v = ∑ j, b.repr ⟨v, hvL'⟩ j • e j := by
      have := congrArg Subtype.val (b.sum_repr ⟨v, hvL'⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have hc : ∀ i, b.repr ⟨v, hvL'⟩ i = 0 := by
      intro i
      have h := hvf i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hv', map_sum] at h
      simpa [map_smul, hfe] using h
    have h0 : (⟨v, hvL'⟩ : L) = 0 := b.repr.injective (by ext i; simp [hc])
    simpa using congrArg Subtype.val h0
  have hdimU := LinearMap.BilinForm.finrank_orthogonal hnd U
  rw [hUo, finrank_bot] at hdimU
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_le U
  simp only [Module.finrank_fin_fun] at hdimU this ⊢
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointOfIntegralPoint
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.Pj.PointsOfFlagModel GlobalTheory.ShFam.Pad.Pull

namespace GlobalTheory.ModelPt

theorem exists_ptC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (C : SCF p) (z : Sp ↥(intO ↥C.S) ⟶ Z.X), Set.range (spMap (intO ↥C.S).subtype ≫ z) ⊆ Z.opn → ∃ P : PointsOfFlagModel.PtC (Y Z.i) C, z ≫ Z.π = P.yt := by
  intro E _ _ _ H Dw Xo p W Y i₀ _ _ Z C z hz
  set w : Sp ↥C.S ⟶ Z.X := spMap (intO ↥C.S).subtype ≫ z with hw
  obtain ⟨pt⟩ : Nonempty (Sp ↥C.S) := inferInstance
  have hpt : w pt ∈ Z.opn := hz ⟨pt, rfl⟩
  rw [← Z.cover] at hpt
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hpt
  have hsub : Subsingleton (Sp ↥C.S) := inferInstance
  obtain ⟨φ, hφ⟩ := exists_fromSpec (Z.U a).2 w (fun q _ => by
    rw [Subsingleton.elim q pt]; exact ha)
  have hcomp : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => by
    rw [← Spec.map_comp]; rfl
  let fK : Z.i.c.F →+* ↥C.S := φ.comp (Z.alg a)
  let alg : ↥(Z.i.c.V W) →+* ↥(intO ↥C.S) := (Spec.preimage (z ≫ Z.π ≫ (Y Z.i).s)).hom
  have halg : spMap alg = z ≫ Z.π ≫ (Y Z.i).s := Spec.map_preimage _
  have hs := affineOpenChart_comp_structure_eq_spMap Z hφ
  have compat : (intO ↥C.S).subtype.comp alg = fK.comp (Z.i.c.V W).subtype := by
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) ?_)
    change spMap _ = spMap _
    rw [hcomp, hcomp, halg, ← hs, hw, Category.assoc]
  have := (Y Z.i).jQ_open
  let q : Sp ↥C.S ⟶ pullback (Y Z.i).s (spMap (Z.i.c.V W).subtype) :=
    pullback.lift (w ≫ Z.π) (spMap fK) ((Category.assoc _ _ _).trans hs)
  have hq : q ≫ pullback.fst _ _ = w ≫ Z.π := pullback.lift_fst _ _ _
  have hq2 : q ≫ pullback.snd _ _ = spMap fK := pullback.lift_snd _ _ _
  have : IsPreimmersion (spMap (Z.i.c.V W).subtype) :=
    IsPreimmersion.of_isLocalization (R := Z.i.c.V W) (S := Z.i.c.F) (nonZeroDivisors _)
  have hr : Set.range q ⊆ Set.range (Y Z.i).jQ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := range_opn Z hφ ⟨x, rfl⟩
    refine ⟨y, (pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply w]
    exact hy
  let y := IsOpenImmersion.lift _ q hr
  have hy : y ≫ (Y Z.i).jQ = q := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨alg, fK, compat, y, ?_, z ≫ Z.π, ?_, ?_⟩, rfl⟩
  · rw [← (Y Z.i).jQ_over, ← Category.assoc, hy, hq2]
  · rw [halg, Category.assoc]
  · rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, reassoc_of% hy, hq]
    rfl

end GlobalTheory.ModelPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealBilinFormEqSumAdditiveImageIntForms
section
open GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_toReal_span_fintype {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ) : ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (Q : κ → LinearMap.BilinForm ℤ L),
      B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let H := Module.Free.chooseBasis ℚ ℝ
  let S : Finset (Module.Free.ChooseBasisIndex ℚ ℝ) :=
    Finset.univ.biUnion fun p : Module.Free.ChooseBasisIndex ℤ L × Module.Free.ChooseBasisIndex ℤ L =>
      (H.repr (B (b p.1) (b p.2))).support
  let f : S × Module.Free.ChooseBasisIndex ℤ L × Module.Free.ChooseBasisIndex ℤ L → ℚ :=
    fun t => H.repr (B (b t.2.1) (b t.2.2)) t.1
  obtain ⟨⟨D, hD⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  choose m hm using hn
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hD
  have hm' : ∀ t, (m t : ℚ) = D * f t := fun t => by simpa [Submonoid.smul_def] using hm t
  let Q : S → LinearMap.BilinForm ℤ L := fun s => Matrix.toLinearMap₂ b b (fun i k => m (s, i, k))
  let g : S → ℝ →+ ℝ := fun s => (D : ℝ) • ((Rat.castHom ℝ).toAddMonoidHom.comp (H.coord s).toAddMonoidHom)
  have hQb : ∀ s i k, (Q s (b i) (b k) : ℝ) = D * (H.repr (B (b i) (b k)) s : ℝ) := fun s i k => by
    have h1 : Q s (b i) (b k) = m (s, i, k) := Matrix.toLinearMap₂_apply_basis _ _ _ _ _
    rw [h1]
    have := hm' (s, i, k)
    simp only [f] at this
    exact_mod_cast this
  have hQ : ∀ s y z, (Q s y z : ℝ) = g s (B y z) := by
    intro s
    have : toReal (Q s) = B.compr₂ (g s).toIntLinearMap := by
      refine LinearMap.ext_basis b b fun i k => ?_
      rw [toReal_apply, hQb]
      simp [g, H]
    intro y z
    simpa using LinearMap.congr_fun₂ this y z
  refine ⟨S, inferInstance, fun s => H s / D, Q, ?_, fun s => ⟨g s, hQ s⟩⟩
  refine LinearMap.ext_basis b b fun i k => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, hQb, smul_eq_mul]
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD'
  have key : ∀ h r : ℝ, h / D * (D * r) = r * h := fun h r => by field_simp
  have e1 : ∀ x : S, H x / D * (D * (H.repr (B (b i) (b k)) x : ℝ)) = H.repr (B (b i) (b k)) x • H x := fun x => by
    rw [Rat.smul_def]; exact key _ _
  rw [Finset.sum_congr rfl fun x _ => e1 x]
  rw [Finset.sum_coe_sort S (fun x => H.repr (B (b i) (b k)) x • H x)]
  conv_lhs => rw [← H.linearCombination_repr (B (b i) (b k))]
  rw [Finsupp.linearCombination_apply]
  refine Finsupp.sum_of_support_subset _ ?_ (fun (x : Module.Free.ChooseBasisIndex ℚ ℝ) (a : ℚ) => a • H x)
    fun x _ => zero_smul ℚ (H x)
  intro x hx
  exact Finset.mem_biUnion.2 ⟨(i, k), Finset.mem_univ _, hx⟩

theorem exists_sum_toReal_additive_images : ∀ {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ), ∃ (n : ℕ) (w : Fin n → ℝ) (Q : Fin n → LinearMap.BilinForm ℤ L),
      B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := by
  intro L _ _ _ B
  obtain ⟨κ, _, w, Q, h1, h2⟩ := exists_toReal_span_fintype B
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun j => w (e.symm j), fun j => Q (e.symm j), ?_, fun j => h2 _⟩
  rw [h1]
  exact (e.symm.sum_comp fun s => w s • toReal (Q s)).symm

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIndependentBasisLatticeFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exists_isLatBasis_of_isLatFam : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → ∃ (r : ℕ) (b : Fin r → Fin g → ℂ), IsLatBasis (K b₀) b := by
  intro n g B K b₀ hK hb₀
  obtain ⟨H, hH⟩ := hK.2.1 b₀ hb₀
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := by rw [← hH]; exact H.zero_mem
  obtain ⟨ζ, hζ0, -, hζ⟩ := hK.2.2.2 b₀ hb₀ 0 h0
  have hcont : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
    (Continuous.prodMk continuous_const continuous_id).tendsto' _ _ rfl
  have hev : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ K b₀ → w = 0 := by
    filter_upwards [hcont.eventually hζ] with w hw hwK
    rw [← hζ0]; exact hw.1 hwK
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule H
  have hL : ∀ w, w ∈ L ↔ w ∈ K b₀ := fun w => by
    rw [← hH]; rfl
  haveI : DiscreteTopology L := by
    obtain ⟨U, hU, hUo, h0U⟩ := mem_nhds_iff.1 hev
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have : ({0} : Set L) = Subtype.val ⁻¹' U := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact h0U
      · intro hx; exact Subtype.ext (hU hx ((hL x).1 x.2))
    rw [this]; exact hUo.preimage continuous_subtype_val
  let bs := Module.finBasis ℤ L
  refine ⟨Module.finrank ℤ L, fun i => (bs i : Fin g → ℂ), GlobalTheory.linearIndependent_real_coe_basis bs, fun w => ?_⟩
  have hsp := GlobalTheory.span_range_coe_basis bs
  have hw : w ∈ L ↔ w ∈ Submodule.span ℤ (Set.range fun i => (bs i : Fin g → ℂ)) := by rw [hsp]
  rw [← hL, hw, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩

end GlobalTheory.ShFam.Hor.LogCh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleUniformisationRigidification
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigRescale

open GlobalTheory GlobalTheory.ArchMetricCompare

theorem exists_rescale_rig : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (rig : LB.Gen (L.pull (eSec A))), L.IsLB → rig.IsGen → ∃ (u' : HolUnif A L g) (lam : ℂ), lam ≠ 0 ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsRig rig ∧ ∀ i z, u'.fr i z = lam * u.fr i z := by
  intro A _ L g u rig hL hr
  have h0 : (u.ex 0).left = eSec A := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp [eSec]
  obtain ⟨j₀, hj₀⟩ := exists_chart_at hL (u.ex 0).left
  have hj₀' : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ (L.pull (eSec A)).U (fun _ => j₀) := by
    exact (le_pull_iff L (eSec A) (𝟙 (Sp ℂ)) (fun _ => j₀)).2 (by rw [Category.id_comp, ← h0]; exact hj₀)
  have hr₀ := valAt'_unit_ne_zero _ hj₀' (rig.s (fun _ => j₀))
  have hf₀ : u.fr j₀ 0 ≠ 0 := u.fr_ne j₀ 0 hj₀
  set r₀ := valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U (fun _ => j₀)) (rig.s (fun _ => j₀)).val with hr₀def
  let u' : HolUnif A L g :=
    { u with
      fr := fun i z => r₀ / u.fr j₀ 0 * u.fr i z
      fr_hol := fun i => (u.fr_hol i).const_mul _
      fr_ne := fun i z h => mul_ne_zero (div_ne_zero hr₀ hf₀) (u.fr_ne i z h)
      fr_compat := fun i j z h => by
        show r₀ / u.fr j₀ 0 * u.fr i z = _ * (r₀ / u.fr j₀ 0 * u.fr j z)
        rw [u.fr_compat i j z h]; ring }
  refine ⟨u', r₀ / u.fr j₀ 0, div_ne_zero hr₀ hf₀, rfl, rfl, ?_, fun _ _ => rfl⟩
  intro j hj
  have hj1 : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ (L.pull (eSec A)).U j := fun p _ => hj trivial
  have hm : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ ((L.pull (eSec A)).U j ⊓ (L.pull (eSec A)).U (fun _ => j₀)) :=
    (top_le_preimage_inf _ _ _).2 ⟨hj1, hj₀'⟩
  have hz : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U j₀) := by
    rw [top_le_preimage_inf, h0]
    exact ⟨by simpa only [Category.id_comp] using (le_pull_iff L (eSec A) (𝟙 (Sp ℂ)) j).1 hj1, by rw [← h0]; exact hj₀⟩
  have e := congrArg (fun a => valAt' (𝟙 (Sp ℂ)) _ (Units.val a)) (hr j (fun _ => j₀))
  simp only [Units.val_mul] at e
  rw [valAt'_mul] at e
  have e1 := (valAt'_res _ inf_le_left _ hm).symm.trans (e.trans (congrArg _ (valAt'_res _ inf_le_right _ hm)))
  have hg := val_pull_g L (eSec A) (𝟙 (Sp ℂ)) j (fun _ => j₀) hm
  rw [Category.id_comp] at hg
  have hc := u.fr_compat (j PUnit.unit) j₀ 0 hz
  rw [h0] at hc
  show r₀ / u.fr j₀ 0 * u.fr (j PUnit.unit) 0 = _
  rw [e1, hg, hc, ← hr₀def]
  field_simp

end GlobalTheory.RigRescale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpModelFiberEqOneIffMemPeriodLattice
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh.PushKer

theorem unit_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem one_left {S T : Scheme.{0}} (a : T ⟶ S) (G : Over S) [MonObj G] :
    (1 : Over.mk a ⟶ G).left = a ≫ (η[G]).left := by
  rw [Hom.one_def]; simp

theorem one_iff {S T : Scheme.{0}} {a : T ⟶ S} {G : Over S} [MonObj G] (x : Over.mk a ⟶ G) :
    x = 1 ↔ x.left = a ≫ (η[G]).left := by
  rw [← one_left]
  exact ⟨fun h => h ▸ rfl, fun h => Over.OverMorphism.ext h⟩

end GlobalTheory.ShFam.Hor.LogCh.PushKer

namespace GlobalTheory.ShFam.Hor.LogCh

open PushKer

theorem pushEx_eq_one_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ z, pushEx Z Fu y i P p hu hp z = 1 ↔ z ∈ P.range := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP z
  rw [← Fu.ex_ker i P hP z, one_iff, one_iff, pushEx_left]
  have u0 := unit_comp Z.m0.toSABMap.cart
  have u1 := unit_comp Z.m.cart
  have hs : (η[Z.oF.t.G]).left ≫ Z.oF.t.G.hom = 𝟙 (Xo.XF c) := Over.w (η[Z.oF.t.G])
  constructor
  · intro h
    have e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left := by
      apply Z.m.cart.1.hom_ext
      · rw [h, Category.assoc, u1, ← hp]
        simp only [Model.j, Category.assoc]
      · rw [liftEx_snd, Category.assoc, hs, Category.comp_id]
    rw [← liftEx_fst Z Fu y i P hu z, e, Category.assoc, u0, hu, Category.assoc]
  · intro h
    have e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left := by
      apply Z.m0.toSABMap.cart.1.hom_ext
      · rw [liftEx_fst, h, Category.assoc, u0, hu, Category.assoc]
      · rw [liftEx_snd, Category.assoc, hs, Category.comp_id]
    rw [e, Category.assoc, u1, ← hp]
    simp only [Category.assoc]

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImRealCombinationEqDotProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.hermForm_im_real_comb (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ i j, (hermForm Hm (x i) (x j)).im = M i j) (u v : Fin r → ℝ) :
    (hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)).im = u ⬝ᵥ M *ᵥ v := by
  have key : hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)
      = ∑ m, ∑ m', ((u m * v m' : ℝ) : ℂ) * hermForm Hm (x m) (x m') := by
    simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct,
      dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    push_cast
    ring
  rw [key]
  simp only [Complex.im_sum, Complex.im_ofReal_mul, h, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  ring
end

