module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairs
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabDense

section Generic

theorem units_tendsto {M ι : Type} [Monoid M] [TopologicalSpace M] {l : Filter ι} {f : ι → Mˣ} {u : Mˣ}
    (h1 : Filter.Tendsto (fun i => (f i : M)) l (nhds (u : M)))
    (h2 : Filter.Tendsto (fun i => (((f i)⁻¹ : Mˣ) : M)) l (nhds ((u⁻¹ : Mˣ) : M))) :
    Filter.Tendsto f l (nhds u) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact h1.prodMk_nhds (MulOpposite.continuous_op.continuousAt.tendsto.comp h2)

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem cut_mul {a b : A} (hab : a * b = 0) (m : Matrix n n A) :
    (a + b) • m + (1 - (a + b)) • (1 : Matrix n n A) =
      (a • m + (1 - a) • (1 : Matrix n n A)) * (b • m + (1 - b) • (1 : Matrix n n A)) := by
  simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul]
  linear_combination (norm := module) hab • (2 • m - m * m - 1)

omit [Fintype n] in
theorem cut_entry (a : A) (m : Matrix n n A) (i j : n) :
    (a • m + (1 - a) • (1 : Matrix n n A)) i j = a * (m - 1) i j + (1 : Matrix n n A) i j := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

omit [Fintype n] in
theorem cut_supp {a : A} (ha : a * a = a) (m : Matrix n n A) (i j : n) :
    a * (a • m + (1 - a) • (1 : Matrix n n A) - 1) i j = (a • m + (1 - a) • (1 : Matrix n n A) - 1) i j := by
  rw [Matrix.sub_apply, cut_entry, add_sub_cancel_right, ← mul_assoc, ha]

theorem sum_idem {R ι : Type} [CommRing R] (p : ι → R) (s : Finset ι) (h : ∀ i, p i * p i = p i)
    (h0 : ∀ i j, i ≠ j → p i * p j = 0) : (∑ i ∈ s, p i) * (∑ i ∈ s, p i) = ∑ i ∈ s, p i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => h0 i j (Ne.symm hji)) (fun hi' => absurd hi hi'), h i]

end Generic

variable {D : D7}

theorem exists_placeIdem (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ ε, IsPlaceIdem D v ε := by
  classical
  refine ⟨pairA D.host.F 0 (singleV D.host.F v 1), singleV D.host.F v 1, rfl, ?_, fun w hw => ?_⟩
  · exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) v 1
  · exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 hw

theorem placeIdem_mul {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, hα0⟩ := h
  obtain ⟨α', rfl, -, hα0'⟩ := h'
  have hz : α * α' = 0 := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    show α w * α' w = 0
    by_cases hw : w = v
    · have hw' : α' w = 0 := hα0' w (by rw [hw]; exact hv)
      rw [hw', mul_zero]
    · have hw' : α w = 0 := hα0 w hw
      rw [hw', zero_mul]
  rw [show pairA D.host.F 0 α * pairA D.host.F 0 α' = pairA D.host.F (0 * 0) (α * α') from rfl, hz, mul_zero]
  rfl

theorem placeIdem_idem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    ε * ε = ε := by
  obtain ⟨α, rfl, hα1, hα0⟩ := h
  have hz : α * α = α := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    show α w * α w = α w
    by_cases hw : w = v
    · have hw' : α w = 1 := by rw [hw]; exact hα1
      rw [hw', mul_one]
    · have hw' : α w = 0 := hα0 w hw
      rw [hw', mul_zero]
  rw [show pairA D.host.F 0 α * pairA D.host.F 0 α = pairA D.host.F (0 * 0) (α * α) from rfl, hz, mul_zero]

theorem mt_inj (V : HSp D) {g h : GA D V} (e : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V h) : g = h := by
  apply Subtype.ext
  apply Units.ext
  exact e

theorem tendsto_of_mt {ι : Type} {l : Filter ι} (V : HSp D) {f : ι → GA D V} {g : GA D V}
    (h1 : Filter.Tendsto (fun i => Formalism.L2.Theta.mt V (f i)) l (nhds (Formalism.L2.Theta.mt V g)))
    (h2 : Filter.Tendsto (fun i => Formalism.L2.Theta.mt V (f i)⁻¹) l (nhds (Formalism.L2.Theta.mt V g⁻¹))) :
    Filter.Tendsto f l (nhds g) := by
  have hind : Topology.IsInducing
      (Subtype.val : ↥(HR (AF D.host.F) D.sp.cm.sig V.gram) → GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    Topology.IsInducing.subtypeVal
  exact hind.tendsto_nhds_iff.2 (units_tendsto h1 h2)

theorem infPart_entry (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  have h1 : infHom V g = 1 := (MonoidHom.mem_ker).1 hg
  have h2 := congrArg (fun x : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) h1
  simp only [infHom, MonoidHom.comp_apply, Formalism.UG.bc] at h2
  have e1 : infPart D (Formalism.L2.Theta.mt V g i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := h2
  have e2 : infPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [Matrix.sub_apply, map_sub, e1, e2, sub_self]

theorem exists_trunc (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F) (hε : ∀ v, IsPlaceIdem D v (ε v))
    (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    ∃ κ : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V → GA D V,
      (∀ g, κ ∅ g = 1) ∧
      (∀ v s (hv : v ∉ s) g, κ (Finset.cons v s hv) g = κ {v} g * κ s g) ∧
      (∀ v g, Stab V β g → Stab V β (κ {v} g) ∧ SuppPl (ε v) V (κ {v} g)) ∧
      ∀ g, Stab V β g → Filter.Tendsto (fun s => κ s g) Filter.atTop (nhds g) := by
  have hid : ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.F)), (∑ v ∈ s, ε v) * (∑ v ∈ s, ε v) = ∑ v ∈ s, ε v :=
    fun s => sum_idem ε s (fun v => placeIdem_idem (hε v)) (fun v w hvw => placeIdem_mul (hε v) (hε w) hvw)
  choose K hK using fun s => _root_.GlobalTheory.UnitaryIdemCut.exists_cut D V β (∑ v ∈ s, ε v) (hid s)
  have hKm : ∀ s x, Formalism.L2.Theta.mt V (K s x) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v) • Formalism.L2.Theta.mt V x +
      (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :=
    fun s x => (hK s x).1
  refine ⟨fun s g => K s g, fun g => ?_, fun v s hv g => ?_, fun v g hg => ⟨(hK {v} g).2 hg, fun i j => ?_⟩, fun g hg => ?_⟩
  · apply mt_inj V
    rw [hKm, Finset.sum_empty, map_zero, zero_smul, sub_zero, one_smul, zero_add, GlobalTheory.AdelicLatMove.mt_one]
  · apply mt_inj V
    show Formalism.L2.Theta.mt V (K _ g) = Formalism.L2.Theta.mt V (K {v} g * K s g)
    rw [hKm, GlobalTheory.AdelicLatMove.mt_mul, hKm, hKm, Finset.sum_cons, Finset.sum_singleton, map_add (f := _)]
    apply cut_mul
    rw [← map_mul, Finset.mul_sum, Finset.sum_eq_zero (fun w hw => placeIdem_mul (hε v) (hε w) (fun hvw => hv (by rw [hvw]; exact hw))), map_zero]
  · show algebraMap (AF D.host.F) (AE D) (ε v) * (Formalism.L2.Theta.mt V (K {v} g) - 1) i j = (Formalism.L2.Theta.mt V (K {v} g) - 1) i j
    rw [hKm, Finset.sum_singleton]
    exact cut_supp (by rw [← map_mul, placeIdem_idem (hε v)]) _ i j
  · have key : ∀ x : GA D V, x ∈ GfC V →
        Filter.Tendsto (fun s => Formalism.L2.Theta.mt V (K s x)) Filter.atTop (nhds (Formalism.L2.Theta.mt V x)) := by
      intro x hx
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      simp only [hKm, cut_entry]
      have hlim := (_root_.GlobalTheory.VecInv.tendsto_truncation D ε hε ((Formalism.L2.Theta.mt V x - 1) i j) (infPart_entry V hx i j)).add_const
        ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
      have e : (Formalism.L2.Theta.mt V x - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j = Formalism.L2.Theta.mt V x i j := by
        rw [Matrix.sub_apply, sub_add_cancel]
      rw [e] at hlim
      exact hlim
    refine tendsto_of_mt V (key g hg.1) ?_
    simpa only [map_inv] using key g⁻¹ (inv_mem hg.1)

theorem mem_of_local (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (H : Subgroup (GA D S × GA D T)) (hH : IsClosed (H : Set (GA D S × GA D T)))
    (hloc : ∀ v ε, IsPlaceIdem D v ε → ∀ g h, Stab S βS g → Stab T βT h → SuppPl ε S g → SuppPl ε T h → (g, h) ∈ H)
    (g : GA D S) (h : GA D T) (hg : Stab S βS g) (hh : Stab T βT h) : (g, h) ∈ H := by
  choose ε hε using fun v => exists_placeIdem (D := D) v
  obtain ⟨κS, hS0, hSc, hS1, hSt⟩ := exists_trunc ε hε S βS
  obtain ⟨κT, hT0, hTc, hT1, hTt⟩ := exists_trunc ε hε T βT
  have hmem : ∀ s, (κS s g, κT s h) ∈ H := by
    intro s
    induction s using Finset.cons_induction with
    | empty => rw [hS0, hT0]; exact H.one_mem
    | cons v s hv ih =>
      rw [hSc v s hv, hTc v s hv]
      exact H.mul_mem (hloc v (ε v) (hε v) _ _ (hS1 v g hg).1 (hT1 v h hh).1 (hS1 v g hg).2 (hT1 v h hh).2) ih
  exact hH.mem_of_tendsto ((hSt g hg).prodMk_nhds (hTt h hh)) (Filter.Eventually.of_forall hmem)

end GlobalTheory.StabDense

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfTypePlaceReductions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemLevRed

theorem mem_lev_of_reductions : ∀ {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (y : GL (Fin T.rank) (EAf D)), LT.Q = ∅ → y ∈ UA D.sp.cm T.gram → y ∈ St βT → ∀ (a b : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1)), (∀ PP, a PP ∈ blockTri (blkOf LT.r LT.t)) → (∀ PP, b PP ∈ blockTri (blkOf LT.r LT.t)) → (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H → (fun PP => upperLeftBlock LT.hr (b PP)) ∈ LT.P.H → (∀ PP : ↥LT.Pg, b PP * redFn βT PP.1 y = a PP) → y ∈ lev D.sp.cm T.gram βT LT := by
  intro D T βT LT y hQ hU hS a b ha hb hHa hHb hab
  have hred : ∀ PP : ↥LT.Pg, redFn βT PP.1 y = (b PP)⁻¹ * a PP := fun PP => by
    rw [← hab PP, inv_mul_cancel_left]
  refine mem_lev.2 ⟨mem_parLev.2 ⟨hU, hS, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
  · rw [hred ⟨PP, hP⟩]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hb ⟨PP, hP⟩)) (ha ⟨PP, hP⟩)
  · rw [hQ] at hP
    exact absurd hP (Finset.notMem_empty PP)
  · have h1 : rTup βT LT y = (fun PP => upperLeftBlock LT.hr (b PP)) ⁻¹ * (fun PP => upperLeftBlock LT.hr (a PP)) := by
      funext PP
      have hb2 := blockTri_blkOf_le LT.r LT.t (hb PP)
      have ha2 := blockTri_blkOf_le LT.r LT.t (ha PP)
      show upperLeftBlock LT.hr (redFn βT PP.1 y) = (upperLeftBlock LT.hr (b PP))⁻¹ * upperLeftBlock LT.hr (a PP)
      rw [hred PP]
      unfold upperLeftBlock
      rw [extendMatrixByIdentityAlongIndices_mul _ (Subgroup.inv_mem _ hb2) ha2, extendOne_inv _ hb2]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hHb) hHa

end GlobalTheory.MemLevRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemMaximalCompactOfMapsFockVectorToFock
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.CompactStab

open scoped ComplexOrder

variable {n : ℕ} {ε : Fin n → Bool}

theorem mem_kset_of_block {h : Matrix (Fin n) (Fin n) ℂ} (hh : hᴴ * Formalism.REAL.Jm ε * h = Formalism.REAL.Jm ε)
    (hb : ∀ j k, ε j ≠ ε k → (hᴴ * h) j k = 0 ∨ (hᴴ * h) k j = 0) : h ∈ Formalism.REAL.Kset ε := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  set J := Formalism.REAL.Jm ε with hJd
  have h1 : (J * hᴴ * J) * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hh, hJ]
  have h2 : h * (J * hᴴ * J) = 1 := mul_eq_one_comm.1 h1
  have h3 : h * J * hᴴ = J := by
    calc h * J * hᴴ = h * J * hᴴ * (J * J) := by rw [hJ, Matrix.mul_one]
      _ = (h * (J * hᴴ * J)) * J := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h2, Matrix.one_mul]
  set P := hᴴ * h with hP
  have hPh : Pᴴ = P := by rw [hP, conjTranspose_mul, conjTranspose_conjTranspose]
  have hb' : ∀ j k, ε j ≠ ε k → P j k = 0 := by
    intro j k hjk
    rcases hb j k hjk with h0 | h0
    · exact h0
    · rw [← hPh, conjTranspose_apply, h0, star_zero]
  have hc : P * J = J * P := by
    ext j k
    simp only [hJd, Formalism.REAL.Jm, mul_diagonal, diagonal_mul]
    by_cases hjk : ε j = ε k
    · rw [hjk, mul_comm]
    · simp [hb' j k hjk]
  have h4 : P * J * P = J := by
    calc P * J * P = hᴴ * (h * J * hᴴ) * h := by simp only [hP, Matrix.mul_assoc]
      _ = J := by rw [h3, hh]
  have h5 : P * P = 1 := by
    calc P * P = (J * J) * P * P := by rw [hJ, Matrix.one_mul]
      _ = J * (P * J * P) := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h4, hJ]
  have h6 : IsUnit (1 + P) :=
    (Matrix.PosDef.add_posSemidef Matrix.PosDef.one (Matrix.posSemidef_conjTranspose_mul_self h)).isUnit
  have h7 : P = 1 := by
    apply h6.mul_left_cancel
    rw [add_mul, h5, one_mul, mul_one, add_comm]
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 h7, ?_⟩
  have h8 : h * hᴴ = 1 := mul_eq_one_comm.1 h7
  calc h * J = h * (hᴴ * J * h) := by rw [hh]
    _ = (h * hᴴ) * J * h := by simp only [Matrix.mul_assoc]
    _ = J * h := by rw [h8, Matrix.one_mul]

theorem exp_iJ_mem (t : ℝ) : NormedSpace.exp (t • (Complex.I • Formalism.REAL.Jm ε)) ∈ Formalism.REAL.Kset ε := by
  have h1 : (Complex.I • Formalism.REAL.Jm ε)ᴴ = -(Complex.I • Formalism.REAL.Jm ε) := by
    rw [conjTranspose_smul, Formalism.REAL.Jm_conjTranspose]; simp
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul, h1,
      star_trivial, smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • (Complex.I • Formalism.REAL.Jm ε))).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  · exact (((Commute.refl (Formalism.REAL.Jm ε)).smul_left _).smul_left t).exp_left

theorem exp_conj_of_mul {a b X : Matrix (Fin n) (Fin n) ℂ} (hab : a * b = 1) (t : ℝ) :
    NormedSpace.exp (t • (a * X * b)) = a * NormedSpace.exp (t • X) * b := by
  have hb : a⁻¹ = b := Matrix.inv_eq_right_inv hab
  have ha : IsUnit a := IsUnit.of_mul_eq_one b hab
  rw [← hb, ← Matrix.exp_conj _ _ ha, Matrix.mul_smul, Matrix.smul_mul]

theorem deriv_mem {Z : Type} (F : Submodule ℂ (Z → ℂ)) [FiniteDimensional ℂ F] {f : ℝ → Z → ℂ} {v : Z → ℂ}
    (hf : ∀ t, f t ∈ F) (hd : ∀ z, HasDerivAt (fun t => f t z) (v z) 0) : v ∈ F := by
  have ht : Filter.Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ) • (f t - f 0)) (nhdsWithin 0 {0}ᶜ) (nhds v) := by
    rw [tendsto_pi_nhds]
    intro z
    have := hasDerivAt_iff_tendsto_slope.1 (hd z)
    refine this.congr fun t => ?_
    simp [slope]
  exact F.closed_of_finiteDimensional.mem_of_tendsto ht
    (Filter.Eventually.of_forall fun t => F.smul_mem _ (F.sub_mem (hf t) (hf 0)))

theorem mem_compact : ∀ (n : ℕ) (ε : Fin n → Bool) (fr G : Matrix (Fin n) (Fin n) ℂ) (σ Z : Type) [Finite σ] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (Z → ℂ)) (L : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (MvPolynomial σ ℂ)), IsUnit fr → frᴴ * Formalism.REAL.Jm ε * fr = G → Function.Injective pt → R 1 = 1 → (∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ g' ∈ Formalism.QuantumDeterminants.UH G, R (g * g') = R g * R g') → (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → ∀ φ z, HasDerivAt (fun t : ℝ => R (NormedSpace.exp (t • X)) (pt φ) z) (pt (L X φ) z) 0) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R (fr⁻¹ * k * fr) (pt φ) = pt ψ) → (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → (∃ j k, ε j ≠ ε k ∧ (fr * X * fr⁻¹) j k ≠ 0 ∧ (fr * X * fr⁻¹) k j ≠ 0) → ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ), FiniteDimensional ℂ F → ¬ ∀ m : ℕ, (L X ^ m) φ ∈ F) → ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ φ φ', φ ≠ 0 → pt φ' = R g (pt φ) → ∃ k ∈ Formalism.REAL.Kset ε, g = fr⁻¹ * k * fr := by
  intro n ε fr G σ Z _ pt R L hfr hG hinj hR1 hmul hder hK hgrow g hg φ φ' hφ hφ'
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hJh := Formalism.REAL.Jm_conjTranspose ε
  set J := Formalism.REAL.Jm ε with hJd
  have hdet := (Matrix.isUnit_iff_isUnit_det fr).1 hfr
  have f1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hdet
  have f2 : fr⁻¹ * fr = 1 := Matrix.nonsing_inv_mul fr hdet
  have f1' : ∀ x : Matrix (Fin n) (Fin n) ℂ, fr * (fr⁻¹ * x) = x := fun x => by
    rw [← Matrix.mul_assoc, f1, Matrix.one_mul]
  have f2' : ∀ x : Matrix (Fin n) (Fin n) ℂ, fr⁻¹ * (fr * x) = x := fun x => by
    rw [← Matrix.mul_assoc, f2, Matrix.one_mul]
  have f3' : ∀ x : Matrix (Fin n) (Fin n) ℂ, (fr⁻¹)ᴴ * (frᴴ * x) = x := fun x => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, f1, conjTranspose_one, Matrix.one_mul]
  have J' : ∀ x : Matrix (Fin n) (Fin n) ℂ, J * (J * x) = x := fun x => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have cU : ∀ x : Matrix (Fin n) (Fin n) ℂ, xᴴ * J * x = J → fr⁻¹ * x * fr ∈ Formalism.QuantumDeterminants.UH G := by
    intro x hx
    show (fr⁻¹ * x * fr)ᴴ * G * (fr⁻¹ * x * fr) = G
    calc (fr⁻¹ * x * fr)ᴴ * G * (fr⁻¹ * x * fr) = frᴴ * (xᴴ * J * x) * fr := by
          simp only [← hG, conjTranspose_mul, Matrix.mul_assoc, f1', f3']
      _ = G := by rw [hx, hG]
  obtain ⟨h, rfl⟩ : ∃ h, g = fr⁻¹ * h * fr := ⟨fr * g * fr⁻¹, by simp only [Matrix.mul_assoc, f2', f2, Matrix.mul_one]⟩
  have hh : hᴴ * J * h = J := by
    have e : (fr⁻¹ * h * fr)ᴴ * G * (fr⁻¹ * h * fr) = G := hg
    have e2 := congrArg (fun x => (fr⁻¹)ᴴ * x * fr⁻¹) e
    simpa only [← hG, conjTranspose_mul, Matrix.mul_assoc, f1', f3', f1, Matrix.mul_one] using e2
  refine ⟨h, mem_kset_of_block hh ?_, rfl⟩
  set h' := J * hᴴ * J with hh'
  have h1 : h' * h = 1 := by
    rw [hh', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hh, hJ]
  have h2 : h * h' = 1 := mul_eq_one_comm.1 h1
  have h3 : h'ᴴ * J * h' = J := by
    calc h'ᴴ * J * h' = J * (h * h') := by
          simp only [hh', conjTranspose_mul, hJh, conjTranspose_conjTranspose, Matrix.mul_assoc, J']
      _ = J := by rw [h2, Matrix.mul_one]
  have hY' : h' * (Complex.I • J) * h = Complex.I • (J * (hᴴ * h)) := by
    simp only [hh', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, J']
  set Y := fr⁻¹ * (h' * (Complex.I • J) * h) * fr with hY
  have hYG : Yᴴ * G + G * Y = 0 := by
    rw [hY, hY']
    simp only [← hG, conjTranspose_mul, conjTranspose_smul, hJh, conjTranspose_conjTranspose, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, J', f1', f3']
    simp
  have cm : ∀ x y : Matrix (Fin n) (Fin n) ℂ, (fr⁻¹ * x * fr) * (fr⁻¹ * y * fr) = fr⁻¹ * (x * y) * fr := by
    intro x y
    simp only [Matrix.mul_assoc, f1']
  have cR : ∀ x y : Matrix (Fin n) (Fin n) ℂ, xᴴ * J * x = J → yᴴ * J * y = J →
      R (fr⁻¹ * (x * y) * fr) = R (fr⁻¹ * x * fr) * R (fr⁻¹ * y * fr) := by
    intro x y hx hy
    rw [← cm, hmul _ (cU x hx) _ (cU y hy)]
  have kU : ∀ k ∈ Formalism.REAL.Kset ε, kᴴ * J * k = J := by
    intro k hk
    have e1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
    have e2 : k * J = J * k := hk.2
    rw [Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have mU : ∀ x y : Matrix (Fin n) (Fin n) ℂ, xᴴ * J * x = J → yᴴ * J * y = J → (x * y)ᴴ * J * (x * y) = J := by
    intro x y hx hy
    calc (x * y)ᴴ * J * (x * y) = yᴴ * (xᴴ * J * x) * y := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J := by rw [hx, hy]
  let F₀ : Submodule ℂ (Z → ℂ) :=
    (MvPolynomial.restrictTotalDegree σ ℂ φ'.totalDegree).map (R (fr⁻¹ * h' * fr) ∘ₗ pt)
  have : FiniteDimensional ℂ F₀ := inferInstance
  have m0 : pt φ ∈ F₀ := by
    refine ⟨φ', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl, ?_⟩
    rw [LinearMap.comp_apply, hφ', ← Module.End.mul_apply, ← cR _ _ h3 hh, h1, Matrix.mul_one, f2, hR1,
      Module.End.one_apply]
  have st : ∀ (t : ℝ), ∀ v ∈ F₀, R (NormedSpace.exp (t • Y)) v ∈ F₀ := by
    rintro t _ ⟨ψ, hψ, rfl⟩
    have hk := exp_iJ_mem (ε := ε) t
    obtain ⟨ψ', hd, he⟩ := hK _ hk ψ
    refine ⟨ψ', (MvPolynomial.mem_restrictTotalDegree _ _ _).2
      (hd.trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 hψ)), ?_⟩
    rw [hY, exp_conj_of_mul f2, exp_conj_of_mul h1, LinearMap.comp_apply, LinearMap.comp_apply, ← he,
      ← Module.End.mul_apply, ← Module.End.mul_apply, ← cR _ _ h3 (kU _ hk),
      ← cR _ _ (mU _ _ (mU _ _ h3 (kU _ hk)) hh) h3, Matrix.mul_assoc _ h, h2, Matrix.mul_one]
  have hm : ∀ m : ℕ, (L Y ^ m) φ ∈ F₀.comap pt := by
    intro m
    induction m with
    | zero => exact m0
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact deriv_mem F₀ (fun t => st t _ ih) (hder Y hYG _)
  have hF : FiniteDimensional ℂ (F₀.comap pt) :=
    FiniteDimensional.of_injective (pt.submoduleComap F₀) (by
      intro a b hab
      exact Subtype.ext (hinj (congrArg Subtype.val hab)))
  intro j k hjk
  by_contra hc
  rw [not_or] at hc
  refine hgrow Y hYG ⟨j, k, hjk, ?_⟩ φ hφ _ hF hm
  have e : fr * Y * fr⁻¹ = Complex.I • (J * (hᴴ * h)) := by
    rw [hY, hY']
    simp only [Matrix.mul_assoc, f1', f1, Matrix.mul_one]
  rw [e]
  simp only [hJd, Formalism.REAL.Jm, Matrix.smul_apply, diagonal_mul, smul_eq_mul]
  constructor
  · refine mul_ne_zero Complex.I_ne_zero (mul_ne_zero ?_ hc.1)
    split_ifs <;> norm_num
  · refine mul_ne_zero Complex.I_ne_zero (mul_ne_zero ?_ hc.2)
    split_ifs <;> norm_num

end GlobalTheory.Chain.RealIt.CompactStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MonomialMemRangeGlue
section
noncomputable section

namespace GlobalTheory.MonomialRangeMembership

open MvPolynomial

theorem monomial_mem_range_glue {D : Formalism.BasicNotions.D7} {a b : ℕ}
    (m : Formalism.IndefR.Datum.FVar D b a →₀ ℕ) :
    (monomial m (1 : ℂ) : Formalism.IndefR.Links.PolF D b a) ∈
      Set.range (GlobalTheory.Chain.RealIt.glue (D := D) (a := a) (b := b)) := by
  refine ⟨fun τ => ∏ s : Fin b × Fin a, X s ^ m (τ, s), ?_⟩
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  unfold GlobalTheory.Chain.RealIt.glue
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [map_prod, map_pow, rename_X]

theorem span_range_glue : ∀ {D : Formalism.BasicNotions.D7} {a b : Nat}, @Eq (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.span Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing) (@Set.range (Formalism.IndefR.Links.PolF D b a) (@Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.what₂ D) → GlobalTheory.Chain.RealIt.LPol b a) (@GlobalTheory.Chain.RealIt.glue D a b))) (@Top.top (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.instTop Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing))) := by
  intro D a b
  rw [eq_top_iff, ← (basisMonomials (Formalism.IndefR.Datum.FVar D b a) ℂ).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  rw [coe_basisMonomials]
  exact monomial_mem_range_glue m

end GlobalTheory.MonomialRangeMembership
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.GivenOfTop

theorem given_of_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → Given R.toRealDat F.lv2 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hH hP hc hQ hG
  exact ⟨(GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx).1, hP, hOk.ok2.irr, hG, hQ, hH.gapR⟩

end GlobalTheory.GivenOfTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminorms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KernelSeminorm

theorem thetaGrowth_onObjects : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D :=
  fun D => GlobalTheory.KernelSeminorm.thetaGrowth D

end GlobalTheory.KernelSeminorm
end

