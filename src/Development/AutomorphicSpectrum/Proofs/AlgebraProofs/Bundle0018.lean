module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.WeilBound.CoreStatements.SesquilinearFractions.UltrametricNormProdSubLt
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LinearIndependentMapVec
section
noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubFrob

variable {K : Type} [Field K]

theorem repr_semilinear {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ} (b : Module.Basis (Fin n) K V)
    (b' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j)) (x : V) (j : Fin n) :
    b'.repr (F x) j = σ (b.repr x j) := by
  have hx : F x = ∑ k, σ (b.repr x k) • b' k := by
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.map_smulₛₗ, h]
  rw [hx, b'.repr_sum_self]

theorem det_semilinear {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ} (b c : Module.Basis (Fin n) K V)
    (b' c' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j)) (hc : ∀ j, c' j = F (c j)) :
    b'.det c' = σ (b.det c) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp only [Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hc]
  exact repr_semilinear F b b' h _ _

theorem isLatOf_spanLat (C : ACurve K) {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ}
    (L : C.I → AddSubgroup V) (i : C.I) (hσ : ∀ a, C.v i a ≤ 1 → C.v i (σ a) ≤ 1)
    (b : Module.Basis (Fin n) K V) (b' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j))
    (hL : IsLatOf C i b (L i)) : IsLatOf C i b' (spanLat C L F i) := by
  intro y
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, x, ha, hx, rfl⟩ := hy
      intro q
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, repr_semilinear F b b' h]
      exact mul_le_one' ha (hσ _ ((hL x).1 hx q))
    | zero => intro q; simp
    | add x y _ _ hx hy =>
      intro q
      rw [map_add (f := _), Finsupp.add_apply]
      exact (C.v i).map_add_le (hx q) (hy q)
    | neg x _ hx =>
      intro q
      rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]
      exact hx q
  · intro hy
    rw [← b'.sum_repr y]
    refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ⟨_, b k, hy k, ?_, by rw [h]⟩
    rw [hL]
    intro q
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem isLatOf_comap (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V] (i : C.I)
    {m r : ℕ} (L : AddSubgroup V) (W : Submodule K V) (b : Module.Basis (Fin (m + r)) K V)
    (c : Module.Basis (Fin m) K W) (h : ∀ j, b (Fin.castAdd _ j) = c j) (hL : IsLatOf C i b L) :
    IsLatOf C i c (L.comap W.subtype.toAddMonoidHom) := by
  intro x
  have hx : (x : V) = ∑ k, (Fin.addCases (motive := fun _ => K) (fun j => c.repr x j) (fun _ => 0) k) • b k := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, zero_smul, Finset.sum_const_zero, add_zero, h]
    have := congrArg W.subtype (c.sum_repr x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    exact this.symm
  have hr : ∀ k, b.repr (x : V) k =
      Fin.addCases (motive := fun _ => K) (fun j => c.repr x j) (fun _ => 0) k := by
    intro k
    conv_lhs => rw [hx, b.repr_sum_self]
  rw [AddSubgroup.mem_comap]
  change (x : V) ∈ L ↔ _
  rw [hL]
  constructor
  · intro H q
    have := H (Fin.castAdd _ q)
    rwa [hr, Fin.addCases_left] at this
  · intro H q
    rw [hr]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) q
    · rw [Fin.addCases_left]; exact H j
    · rw [Fin.addCases_right]; simp

def mapVec (σ : K →+* K) (d : ℕ) : (Fin d → K) →ₛₗ[σ] (Fin d → K) where
  toFun x := fun j => σ (x j)
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

theorem linearIndependent_mapVec (σ : K →+* K) {d n : ℕ} (v : Fin n → Fin d → K)
    (hv : LinearIndependent K v) : LinearIndependent K (fun j => mapVec σ d (v j)) := by
  have h1 : Function.Injective (Matrix.of v).vecMulLinear := by
    have := Matrix.vecMul_injective_iff.2 (show LinearIndependent K (Matrix.of v).row from hv)
    exact this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 h1)
  set B : Matrix (Fin d) (Fin n) K := LinearMap.toMatrixRight' g with hB
  have hgB : ∀ x, g x = Matrix.vecMul x B := by
    intro x
    have : Matrix.toLinearMapRight' B = g := by
      rw [hB]; exact LinearMap.toMatrixRight'.symm_apply_apply g
    rw [← this]; rfl
  have h2 : Matrix.of v * B = 1 := by
    ext a b
    have := congrFun (LinearMap.congr_fun hg (Pi.single a 1)) b
    simp only [LinearMap.comp_apply, hgB, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul,
      LinearMap.id_apply, Matrix.single_one_vecMul] at this
    rw [Matrix.one_apply]
    change Matrix.vecMul (v a) B b = _
    simpa [Pi.single_apply, eq_comm] using this
  have h3 : (Matrix.of v).map σ * B.map σ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ σ.map_zero σ.map_one]
  have h4 : LinearIndependent K ((Matrix.of v).map σ).row := by
    rw [← Matrix.vecMul_injective_iff]
    intro x y hxy
    have := congrArg (fun z => Matrix.vecMul z (B.map σ)) hxy
    simpa [Matrix.vecMul_vecMul, h3] using this
  exact h4

theorem exists_basis_top (σ : K →+* K) {d n : ℕ} (b : Module.Basis (Fin n) K (Fin d → K)) :
    ∃ b' : Module.Basis (Fin n) K (Fin d → K), ∀ j, b' j = mapVec σ d (b j) :=
  ⟨basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_mapVec σ b b.linearIndependent)
    (Module.finrank_eq_card_basis b).symm, fun j => by simp⟩

theorem exists_basis_sub (σ : K →+* K) {d n : ℕ} (W : Submodule K (Fin d → K))
    (c : Module.Basis (Fin n) K W) :
    ∃ c' : Module.Basis (Fin n) K (Submodule.span K (mapVec σ d '' (W : Set (Fin d → K)))),
      ∀ j, (c' j : Fin d → K) = mapVec σ d (c j) := by
  have hli := linearIndependent_mapVec σ (fun j => (c j : Fin d → K))
    (c.linearIndependent.map' W.subtype W.ker_subtype)
  have hs : Submodule.span K (Set.range fun j => mapVec σ d (c j)) =
      Submodule.span K (mapVec σ d '' (W : Set (Fin d → K))) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨c j, (c j).2, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have : x = ∑ k, c.repr ⟨x, hx⟩ k • (c k : Fin d → K) := by
        have := congrArg W.subtype (c.sum_repr ⟨x, hx⟩)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum] at this
        exact this.symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨(Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hs), fun j => ?_⟩
  simp [Module.Basis.span_apply]

theorem subDeg_frob : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W : Submodule K (Fin d → K)), IsBun C L → subDeg C (frobLat C p L) (frobSub p W) = p * subDeg C L W := by
  intro K _ C p _ _ d L W hL
  set σ := frobenius K p with hσ
  have hL' : IsBun C (frobLat C p L) := (_root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat K C p d L hL).1
  have hS := (_root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C _ L W hL).1
  have hS' := (_root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C _ _ (frobSub p W) hL').1
  have hv : ∀ i a, C.v i (σ a) = C.v i a ^ p := fun i a => by rw [hσ, frobenius_def, map_pow]
  have key : ∀ i, ∃ (c : Module.Basis (Fin (Module.finrank K W)) K W)
      (c' : Module.Basis (Fin (Module.finrank K W)) K (frobSub p W)),
      IsLatOf C i c (sub C L W i) ∧ IsLatOf C i c' (sub C (frobLat C p L) (frobSub p W) i) ∧
      ∀ j, (c' j : Fin d → K) = mapVec σ d (c j) := by
    intro i
    obtain ⟨b, hb⟩ := hL.1 i
    obtain ⟨c, -, b₁, hb₁, hc, -, hbc, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C _ i _ b (L i) W hb
    obtain ⟨b', hb'⟩ := exists_basis_top σ b₁
    obtain ⟨c', hc'⟩ := exists_basis_sub σ W c
    refine ⟨c, c', hc, ?_, hc'⟩
    refine isLatOf_comap C i _ _ b' c' (fun j => by rw [hb', hbc]; exact (hc' j).symm) ?_
    exact isLatOf_spanLat C (mapVec σ d) L i (fun a ha => by rw [hv]; exact pow_le_one' ha p)
      b₁ b' hb' hb₁
  choose c c' hc hc' hcc using key
  obtain ⟨e', he'⟩ : ∃ e' : Module.Basis (Fin (Module.finrank K W)) K (frobSub p W),
      ∀ j, (e' j : Fin d → K) = mapVec σ d (Module.finBasis K W j) :=
    exists_basis_sub σ W (Module.finBasis K W)
  let G : W →ₛₗ[σ] frobSub p W :=
    ((mapVec σ d).domRestrict W).codRestrict (frobSub p W)
      (fun x => Submodule.subset_span ⟨x, x.2, rfl⟩)
  obtain ⟨-, h1⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C _ _ _ (Module.finBasis K W) c hS hc
  obtain ⟨-, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C _ _ _ e' c' hS' hc'
  unfold subDeg
  rw [h1, h2, mul_finsum]
  refine finsum_congr fun i => ?_
  have hd := det_semilinear G (Module.finBasis K W) (c i) e' (c' i)
    (fun j => Subtype.ext (he' j)) (fun j => Subtype.ext (hcc i j))
  rw [hd, hv, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Crv.SubFrob
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NegDefBlockOfPosDef
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.Sylvester

theorem neg_posDef_of_compl_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef :=
  @PositivityTheory.Xgf.negDef_block_of_posDef

end GlobalTheory.CompanionTheory.Ar.Fl.Sylvester
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwoMulFinrank
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

namespace PtBasic

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

theorem ht_surjective : Function.Surjective P.ht := by
  have : P.om.IsFullLattice C := P.om_lat
  have hspan : Submodule.span C (P.om : Set Ω) = ⊤ := Submodule.IsFullLattice.span_eq_top
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
  intro y hy
  obtain ⟨x, -, hx⟩ := P.κ_mem y hy
  show y ∈ LinearMap.range P.ht
  rw [LinearMap.mem_range]
  refine ⟨(algebraMap O C κ)⁻¹ • x, ?_⟩
  rw [map_smul, hx, ← algebraMap_smul C κ y, smul_smul, inv_mul_cancel₀ P.κ_ne, one_smul]

theorem T_lattice : P.T.IsLattice C := by
  obtain ⟨hli, -, hT⟩ := P.free
  have hfg : P.T.FG := by
    rw [hT]
    exact Submodule.fg_span (Set.finite_range _)
  refine ⟨hfg, ?_⟩
  intro s hs hliO
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact linearIndepOn_empty C id
  have hinj : Function.Injective (algebraMap O C) := by
    intro a b hab
    apply hliO.linearIndependent.smul_left_injective ⟨x, hx⟩
    change a • x = b • x
    rw [← algebraMap_smul C a x, ← algebraMap_smul C b x, hab]
  have : FaithfulSMul O C := (faithfulSMul_iff_algebraMap_injective O C).mpr hinj
  have : Nontrivial O := (algebraMap O C).domain_nontrivial
  refine Submodule.linearIndepOn_of_finrank_le_finrank_span P.T hfg ?_ hs hliO
  rw [hT, Submodule.span_span_of_tower O, finrank_span_eq_card hli,
    finrank_span_eq_card (hli.restrict_scalars' O)]

theorem rho_t_mem (a : 𝓞 E) (i : Fin N) : P.ρ a (P.t i) ∈ P.T := by
  obtain ⟨-, -, hT⟩ := P.free
  have hmem : ∀ k, P.ρ (RingOfIntegers.basis E k) (P.t i) ∈ P.T := fun k => by
    rw [hT]
    exact Submodule.subset_span ⟨(i, k), rfl⟩
  rw [← (RingOfIntegers.basis E).sum_repr a]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun k _ => zsmul_mem (hmem k) _

theorem T_stable (a : 𝓞 E) : ∀ x ∈ P.T, P.ρ a x ∈ P.T := by
  obtain ⟨-, -, hT⟩ := P.free
  have hle : P.T ≤ P.T.comap ((P.ρ a).restrictScalars O) := by
    nth_rewrite 1 [hT]
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    show P.ρ a (P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) ∈ P.T
    rw [show P.ρ a (P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) =
        (P.ρ a * P.ρ (RingOfIntegers.basis E q.2)) (P.t q.1) from rfl, ← map_mul]
    exact rho_t_mem P _ _
  exact fun x hx => hle hx

theorem ht_eigProj (σ : E →+* C) (x : V) :
    P.ht (eigProj P.ρ σ x) = eigProj P.ρΩ σ (P.ht x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, P.ht_lin]

theorem om'_lattice : P.om'.IsLattice C := by
  have : P.om.IsFullLattice C := P.om_lat
  apply Submodule.IsLattice.mono_of_fg C (show P.om' ≤ P.om from ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact P.ht_mem x hx
  · rw [HTPoint.om']
    exact (T_lattice P).fg.map _

theorem omHT_eq (σ : E →+* C) :
    P.omHT σ = (eigQuot P.ρ σ P.T).map (P.ht.restrictScalars O) := by
  have hcomm : ((eigProj P.ρΩ σ).restrictScalars O) ∘ₗ (P.ht.restrictScalars O) =
      (P.ht.restrictScalars O) ∘ₗ ((eigProj P.ρ σ).restrictScalars O) :=
    LinearMap.ext fun x => (ht_eigProj P σ x).symm
  show (P.T.map (P.ht.restrictScalars O)).map ((eigProj P.ρΩ σ).restrictScalars O) =
    (P.T.map ((eigProj P.ρ σ).restrictScalars O)).map (P.ht.restrictScalars O)
  rw [← Submodule.map_comp, ← Submodule.map_comp, hcomm]

theorem e_skew (x y : V) : P.e x y = - P.e y x := by
  have h := P.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, P.alt, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem dualLat_flip : dualLat P.e.flip P.T = P.T := by
  conv_rhs => rw [← P.perfect]
  ext y
  simp only [LatBasic.mem_dualLat, LinearMap.flip_apply]
  refine forall₂_congr fun x _ => ?_
  rw [e_skew P y x, neg_mem_iff]
include P in
theorem finite_V : Module.Finite C V := by
  obtain ⟨s, hs⟩ := (T_lattice P).fg
  refine ⟨⟨s, ?_⟩⟩
  rw [← Submodule.span_span_of_tower O, hs, P.free.2.1]
include P in
theorem two_mul_finrank : 2 * finrank C Ω = finrank C V := by
  haveI := finite_V P
  have hrefl : LinearMap.BilinForm.IsRefl P.e := fun x y h => by rw [e_skew P y x, h, neg_zero]
  have horth : LinearMap.BilinForm.orthogonal P.e (LinearMap.ker P.ht) = LinearMap.ker P.ht := by
    ext x
    simp only [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker]
    rw [P.lagr x]
    refine forall₂_congr fun y _ => ?_
    rw [e_skew P y x, neg_eq_zero]
  have htop : LinearMap.BilinForm.orthogonal P.e ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    exact (Submodule.mem_bot C).mpr (P.nondeg x fun y => hx y Submodule.mem_top)
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal hrefl (LinearMap.ker P.ht)
  rw [horth, htop, inf_bot_eq, finrank_bot, add_zero] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker P.ht
  rw [LinearMap.range_eq_top.mpr (ht_surjective P), finrank_top] at h2
  omega

end PtBasic

theorem htPoint_basic : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [IsAlgClosed C] [CharZero C] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (κ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω : Type) [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω), Function.Surjective P.ht ∧ P.T.IsLattice C ∧ (∀ (a : 𝓞 E), ∀ x ∈ P.T, P.ρ a x ∈ P.T) ∧ (∀ (σ : E →+* C) x, P.ht (eigProj P.ρ σ x) = eigProj P.ρΩ σ (P.ht x)) ∧ P.om'.IsLattice C ∧ (∀ σ : E →+* C, P.omHT σ = (eigQuot P.ρ σ P.T).map (P.ht.restrictScalars O)) ∧ dualLat P.e.flip P.T = P.T ∧ 2 * Module.finrank C Ω = Module.finrank C V := by
  intro C _ v O _ _ _ _ _ E _ _ c _ κ N V _ _ _ _ Ω _ _ _ _ P
  exact ⟨PtBasic.ht_surjective P, PtBasic.T_lattice P, PtBasic.T_stable P, PtBasic.ht_eigProj P,
    PtBasic.om'_lattice P, PtBasic.omHT_eq P, PtBasic.dualLat_flip P, PtBasic.two_mul_finrank P⟩

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormStable
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem norm_det_eq_of_entries_close : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M M' : Matrix I I A) (r : ℝ), 0 < r → (∀ a b, ‖M a b‖ ≤ r) → (∀ a b, ‖M' a b - M a b‖ < r) → ‖M.det‖ = r ^ Fintype.card I → ‖M'.det‖ = r ^ Fintype.card I :=
  @PositivityTheory.Xgf.ultrametric_det_norm_stable

end GlobalTheory.CompanionTheory.Ar.Fl
end

