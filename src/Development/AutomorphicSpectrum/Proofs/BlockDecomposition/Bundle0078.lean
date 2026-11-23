module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0059
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
public import GroundTheory.AutomorphicForms.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianRepCountFourierExpansion
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.LevelId

variable {R : Type} [CommRing R]

theorem cT_mul (σ : R →+* R) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    cT σ (x * y) = cT σ y * cT σ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_cT (σ : R →+* R) (h : ∀ a, σ (σ a) = a) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    cT σ (cT σ x) = x := by
  ext i j
  exact h (x i j)

theorem cT_sub (σ : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x - y) = cT σ x - cT σ y := by
  ext i j
  exact map_sub σ (x j i) (y j i)

theorem red_mul (ϖ : R) (k : ℕ) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    red ϖ k (x * y) = red ϖ k x * red ϖ k y := by
  unfold red
  exact Matrix.map_mul

theorem red_sub (ϖ : R) (k : ℕ) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k (x - y) = red ϖ k x - red ϖ k y := by
  ext i j
  exact map_sub (Ideal.Quotient.mk (lev ϖ k)) (x i j) (y i j)

theorem red_neg (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (-x) = - red ϖ k x := by
  ext i j
  exact map_neg (Ideal.Quotient.mk (lev ϖ k)) (x i j)

theorem red_cT (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (cT σ x) = cT (barσ σ ϖ h k) (red ϖ k x) := by
  ext i j
  exact (barσ_mk σ ϖ h k (x j i)).symm

theorem red_surj (ϖ : R) (k : ℕ) {a b : ℕ} :
    Function.Surjective (red ϖ k : Matrix (Fin a) (Fin b) R → _) := by
  intro y
  refine ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (y i j)).choose, ?_⟩
  ext i j
  exact (Ideal.Quotient.mk_surjective (y i j)).choose_spec

theorem red_gram (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (x : Matrix (Fin m) (Fin n) R) :
    red ϖ k (cT σ x * S * x) = cT (barσ σ ϖ h k) (red ϖ k x) * red ϖ k S * red ϖ k x := by
  rw [red_mul, red_mul, red_cT σ ϖ h]

theorem image_sol (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) :
    red ϖ k '' {x : Matrix (Fin m) (Fin n) R | red ϖ k (cT σ x * S * x) = red ϖ k T} =
      {y | cT (barσ σ ϖ h k) y * red ϖ k S * y = red ϖ k T} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show cT (barσ σ ϖ h k) (red ϖ k x) * red ϖ k S * red ϖ k x = red ϖ k T
    rw [← red_gram σ ϖ h]
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := red_surj ϖ k y
    refine ⟨x, ?_, rfl⟩
    show red ϖ k (cT σ x * S * x) = red ϖ k T
    rw [red_gram σ ϖ h]
    exact hy

theorem gram_sub_mem (σ : R →+* R) (ϖ : R) (hinv : ∀ a, σ (σ a) = a) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : cT σ S = S) (hT : cT σ T = T)
    (y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) :
    cT (barσ σ ϖ h k) y * red ϖ k S * y - red ϖ k T ∈ hermMod σ ϖ n k := by
  obtain ⟨x, rfl⟩ := red_surj ϖ k y
  unfold hermMod
  refine ⟨cT σ x * S * x - T, ?_, ?_⟩
  · show cT σ (cT σ x * S * x - T) = cT σ x * S * x - T
    rw [cT_sub, cT_mul, cT_mul, cT_cT σ hinv, hS, hT, Matrix.mul_assoc]
  · show red ϖ k (cT σ x * S * x - T) = _
    rw [red_sub, red_gram σ ϖ h]

theorem neg_mem_herm (σ : R →+* R) (ϖ : R) (n k : ℕ) {B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)}
    (hB : B ∈ hermMod σ ϖ n k) : -B ∈ hermMod σ ϖ n k := by
  unfold hermMod at hB ⊢
  obtain ⟨h0, hh, rfl⟩ := hB
  refine ⟨-h0, ?_, red_neg ϖ k h0⟩
  show cT σ (-h0) = -h0
  have hh' : cT σ h0 = h0 := hh
  ext i j
  have e : σ (h0 j i) = h0 i j := congrFun (congrFun hh' i) j
  show σ (-(h0 j i)) = -(h0 i j)
  rw [map_neg, e]

theorem nuAt_neg (ϖ : R) {n k : ℕ} (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :
    nuAt ϖ (-B) = nuAt ϖ B := by
  unfold nuAt
  have hset : (Set.range fun x : Fin n → R ⧸ lev ϖ k => Matrix.vecMul x (-B)) =
      Set.range fun x : Fin n → R ⧸ lev ϖ k => Matrix.vecMul x B := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      show Matrix.vecMul (-x) B = Matrix.vecMul x (-B)
      rw [Matrix.neg_vecMul, Matrix.vecMul_neg]
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      show Matrix.vecMul (-x) (-B) = Matrix.vecMul x B
      rw [Matrix.neg_vecMul, Matrix.vecMul_neg, neg_neg]
  rw [hset]

end GlobalTheory.CompanionTheory.SiegLoc.LevelId


open GlobalTheory.CompanionTheory.SiegLoc.LevelId in
theorem GlobalTheory.CompanionTheory.SiegLoc.level_identity : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (m n k : ℕ) (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), cT σ S = S → cT σ T = T → (∀ Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k), Y ∈ hermMod σ ϖ n k → (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧ (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0)) → (∀ B ∈ hermMod σ ϖ n k, (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ψ k (Matrix.trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) = (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B))) → siegAt ϖ σ ψ q ε m T k = ((densAt σ ϖ S T k : ℝ) : ℂ) := by
  intro R _ σ ϖ q ε hR _ ψ hψ m n k S T hS hT horth hgauss
  classical
  have : Fintype ↥(hermMod σ ϖ n k) := Fintype.ofFinite _
  have hx : ∀ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
      (∑' B : hermMod σ ϖ n k,
        ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x - red ϖ k T)))) =
        if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then
          (Nat.card (hermMod σ ϖ n k) : ℂ) else 0 := by
    intro x
    have hmem := gram_sub_mem σ ϖ hR.inv hR.fix_ϖ k S T hS hT x
    by_cases hxe : cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T
    · rw [if_pos hxe]
      exact (horth _ hmem).1 (sub_eq_zero.mpr hxe)
    · rw [if_neg hxe]
      exact (horth _ hmem).2 (sub_ne_zero.mpr hxe)
  have hsplit : ∀ (B : hermMod σ ϖ n k) (x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)),
      ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x - red ϖ k T))) =
        ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
          ψ k (-Matrix.trace (B.1 * red ϖ k T)) := by
    intro B x
    rw [Matrix.mul_sub, Matrix.trace_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hsol : (solCount σ ϖ S T k : ℂ) = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
      if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0 := by
    unfold solCount
    rw [image_sol σ ϖ hR.fix_ϖ k S T, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.natCast_card_filter]
    exact Finset.sum_congr rfl fun x _ => if_congr Iff.rfl rfl rfl
  have h1 : ∀ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), (Nat.card (hermMod σ ϖ n k) : ℂ) *
      (if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0) =
      ∑ B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
        ψ k (-Matrix.trace (B.1 * red ϖ k T)) := by
    intro x
    rw [mul_ite, mul_one, mul_zero, ← hx x, tsum_fintype]
    exact Finset.sum_congr rfl fun B _ => hsplit B x
  have hcount : (Nat.card (hermMod σ ϖ n k) : ℂ) * (solCount σ ϖ S T k : ℂ) =
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) *
        ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
          ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    calc (Nat.card (hermMod σ ϖ n k) : ℂ) * (solCount σ ϖ S T k : ℂ)
        = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), (Nat.card (hermMod σ ϖ n k) : ℂ) *
            (if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0) := by
          rw [hsol, Finset.mul_sum]
      _ = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ∑ B : hermMod σ ϖ n k,
            ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
              ψ k (-Matrix.trace (B.1 * red ϖ k T)) := Finset.sum_congr rfl fun x _ => h1 x
      _ = ∑ B : hermMod σ ϖ n k, ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
            ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
              ψ k (-Matrix.trace (B.1 * red ϖ k T)) := Finset.sum_comm
      _ = ∑ B : hermMod σ ϖ n k, (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) *
            (ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
              ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1)) := by
          refine Finset.sum_congr rfl fun B _ => ?_
          rw [← Finset.sum_mul, hgauss B.1 B.2]
          ring
      _ = _ := by rw [Finset.mul_sum]
  have hneg : ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) =
      ∑ B : hermMod σ ϖ n k, ψ k (Matrix.trace (red ϖ k T * B.1)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    let e : hermMod σ ϖ n k ≃ hermMod σ ϖ n k :=
      { toFun := fun B => ⟨-B.1, neg_mem_herm σ ϖ n k B.2⟩
        invFun := fun B => ⟨-B.1, neg_mem_herm σ ϖ n k B.2⟩
        left_inv := fun B => Subtype.ext (neg_neg _)
        right_inv := fun B => Subtype.ext (neg_neg _) }
    refine Fintype.sum_equiv e _ _ fun B => ?_
    show _ = ψ k (Matrix.trace (red ϖ k T * -B.1)) *
      ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ (-B.1))
    rw [nuAt_neg, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_mul_comm]
  have hfin : siegAt ϖ σ ψ q ε m T k = ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    unfold siegAt
    rw [tsum_fintype, hneg]
  have hM : (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcast : ((densAt σ ϖ S T k : ℝ) : ℂ) = (solCount σ ϖ S T k : ℂ) * (Nat.card (hermMod σ ϖ n k) : ℂ) /
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) := by
    unfold densAt
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_natCast,
      Complex.ofReal_natCast]
  rw [hfin, hcast, eq_div_iff hM]
  linear_combination (-1 : ℂ) * hcount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalEqHaarMultiple
section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

noncomputable section

namespace GlobalTheory.CompanionTheory.FrobHaarR

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_open_left_stab {F : G → ℂ} (hF : F ∈ SB G) :
    ∃ K : OpenSubgroup G, ∀ k ∈ K, ∀ x, F (k * x) = F x := by
  let K : Subgroup G :=
    { carrier := {k | ∀ g, F (k * g) = F g}
      one_mem' := by intro g; simp
      mul_mem' := by
        intro a b ha hb g
        rw [mul_assoc, ha, hb]
      inv_mem' := by
        intro a ha g
        have := ha (a⁻¹ * g)
        simpa using this.symm }
  have h1 : ∀ᶠ k in nhds (1 : G), ∀ g ∈ tsupport F, F (k * g) = F g := by
    apply IsCompact.eventually_forall_of_forall_eventually hF.2
    intro g _
    have a1 : IsLocallyConstant (fun z : G × G => F (z.1 * z.2)) :=
      hF.1.comp_continuous (by fun_prop)
    have a2 : IsLocallyConstant (fun z : G × G => F z.2) :=
      hF.1.comp_continuous (by fun_prop)
    filter_upwards [a1.eventually_eq (1, g), a2.eventually_eq (1, g)] with z hz1 hz2
    simp only [hz1, hz2, one_mul]
  have h2 : ∀ᶠ k in nhds (1 : G), ∀ g ∈ tsupport F, F (k⁻¹ * g) = F g := by
    have : Filter.Tendsto (fun x : G => x⁻¹) (nhds 1) (nhds 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact this.eventually h1
  have hK : IsOpen (K : Set G) := by
    apply Subgroup.isOpen_of_mem_nhds K (g := 1)
    filter_upwards [h1, h2] with k hk1 hk2
    intro g
    by_cases hg : g ∈ tsupport F
    · exact hk1 g hg
    · by_cases hg' : k * g ∈ tsupport F
      · simpa using (hk2 _ hg').symm
      · rw [image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hg']
  exact ⟨⟨K, hK⟩, fun k hk x => hk x⟩

theorem ind_mem (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Set.indicator (K : Set G) (fun _ => (1 : ℂ)) ∈ SB G := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
    HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (K : Set G)
  · exact ⟨K, K.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(K : Set G)ᶜ, K.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

def ind (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) : SB G :=
  ⟨_, ind_mem K hK⟩

theorem ind_apply (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    (ind K hK : G → ℂ) x = Set.indicator (K : Set G) (fun _ => (1 : ℂ)) x :=
  rfl

theorem ind_left (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) (x : G) :
    (ind K hK : G → ℂ) (k * x) = (ind K hK : G → ℂ) x := by
  have h : k * x ∈ (K : Set G) ↔ x ∈ (K : Set G) :=
    Subgroup.mul_mem_cancel_left K.toSubgroup hk
  by_cases hx : x ∈ (K : Set G)
  · rw [ind_apply, ind_apply, Set.indicator_of_mem (h.2 hx), Set.indicator_of_mem hx]
  · rw [ind_apply, ind_apply, Set.indicator_of_notMem (fun h' => hx (h.1 h')),
      Set.indicator_of_notMem hx]

theorem exists_decomp (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : SB G)
    (hf : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    ∃ (S : Finset G) (a : G → ℂ),
      f = ∑ t ∈ S, a t • pullHomeo (Homeomorph.mulRight t) (ind K hK) := by
  classical
  have hdisc : DiscreteTopology (G ⧸ (K : Subgroup G)) :=
    QuotientGroup.discreteTopology K.isOpen
  let π : G → G ⧸ (K : Subgroup G) := fun x => ((x⁻¹ : G) : G ⧸ (K : Subgroup G))
  have hπ : Continuous π := QuotientGroup.continuous_mk.comp continuous_inv
  have hfin : (π '' tsupport (f : G → ℂ)).Finite :=
    ((show IsCompact (tsupport (f : G → ℂ)) from f.2.2).image hπ).finite_of_discrete
  have key : ∀ (x : G) (q : G ⧸ (K : Subgroup G)), x * q.out ∈ K ↔ π x = q := by
    intro x q
    have h := QuotientGroup.eq (s := (K : Subgroup G)) (a := x⁻¹) (b := q.out)
    rw [inv_inv, QuotientGroup.out_eq'] at h
    exact h.symm
  have hinj : Set.InjOn (fun q : G ⧸ (K : Subgroup G) => q.out) (hfin.toFinset : Set _) :=
    fun a _ b _ h => Quotient.out_injective h
  refine ⟨hfin.toFinset.image (fun q => q.out), fun t => (f : G → ℂ) t⁻¹, ?_⟩
  rw [Finset.sum_image hinj]
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  have hterm : ∀ q ∈ hfin.toFinset,
      ((((f : G → ℂ) q.out⁻¹ • pullHomeo (Homeomorph.mulRight q.out) (ind K hK) : SB G)) : G → ℂ) x
        = if π x = q then (f : G → ℂ) x else 0 := by
    intro q _
    have e : ((((f : G → ℂ) q.out⁻¹ • pullHomeo (Homeomorph.mulRight q.out) (ind K hK) : SB G)) :
        G → ℂ) x = (f : G → ℂ) q.out⁻¹ * (ind K hK : G → ℂ) (x * q.out) := rfl
    rw [e, ind_apply]
    by_cases h : π x = q
    · have hm : x * q.out ∈ K := (key x q).2 h
      rw [if_pos h, Set.indicator_of_mem (show x * q.out ∈ (K : Set G) from hm), mul_one]
      have := hf _ hm q.out⁻¹
      rw [mul_inv_cancel_right] at this
      exact this.symm
    · rw [if_neg h, Set.indicator_of_notMem
        (show x * q.out ∉ (K : Set G) from fun hm => h ((key x q).1 hm)), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra h0
    exact h (hfin.mem_toFinset.2 ⟨x, subset_tsupport _ h0, rfl⟩)

theorem exists_coeff (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : SB G)
    (hf : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    ∃ s : ℂ, ∀ M : SB G →ₗ[ℂ] ℂ,
      (∀ (g : G) (α : SB G), M (pullHomeo (Homeomorph.mulRight g) α) = M α) →
        M f = s * M (ind K hK) := by
  obtain ⟨S, a, h⟩ := exists_decomp K hK f hf
  refine ⟨∑ t ∈ S, a t, fun M hM => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, _root_.map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, hM, smul_eq_mul]

end Abstract

section Integral

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

theorem integrable_sb (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (α : SB G) :
    Integrable (α : G → ℂ) μ :=
  α.2.1.continuous.integrable_of_hasCompactSupport α.2.2

def haarForm (μ : Measure G) [IsFiniteMeasureOnCompacts μ] : SB G →ₗ[ℂ] ℂ where
  toFun α := ∫ x, (α : G → ℂ) x ∂μ
  map_add' α β := integral_add (integrable_sb μ α) (integrable_sb μ β)
  map_smul' c α := integral_const_mul c (α : G → ℂ)

theorem haarForm_apply (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (α : SB G) :
    haarForm μ α = ∫ x, (α : G → ℂ) x ∂μ :=
  rfl

variable [LocallyCompactSpace G]

theorem integral_mul_right_real (hU : IsUnimod G) (μ : Measure G) [μ.IsHaarMeasure] (g : G)
    {u : G → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u) :
    ∫ x, u (x * g) ∂μ = ∫ x, u x ∂μ := by
  have h := integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (map (· * g) μ) μ hu hcu
  have h1 : modularCharacterFun g = 1 := hU g
  rw [integral_smul_nnreal_measure, ← modularCharacterFun_eq_haarScalarFactor μ g, h1, one_smul,
    integral_map (AEMeasurable.mul_const aemeasurable_id' _) hu.aestronglyMeasurable] at h
  exact h

theorem haarForm_right (hU : IsUnimod G) (μ : Measure G) [μ.IsHaarMeasure] (g : G) (α : SB G) :
    haarForm μ (pullHomeo (Homeomorph.mulRight g) α) = haarForm μ α := by
  have hc : Continuous (α : G → ℂ) := α.2.1.continuous
  have hcs : HasCompactSupport (α : G → ℂ) := α.2.2
  have hre := integral_mul_right_real hU μ g (u := fun x => RCLike.re ((α : G → ℂ) x))
    (RCLike.continuous_re.comp hc) (hcs.comp_left (g := RCLike.re) (map_zero _))
  have him := integral_mul_right_real hU μ g (u := fun x => RCLike.im ((α : G → ℂ) x))
    (RCLike.continuous_im.comp hc) (hcs.comp_left (g := RCLike.im) (map_zero _))
  rw [haarForm_apply, haarForm_apply,
    ← integral_re_add_im (integrable_sb μ (pullHomeo (Homeomorph.mulRight g) α)),
    ← integral_re_add_im (integrable_sb μ α)]
  simp only [pullHomeo_apply, Homeomorph.coe_mulRight]
  rw [hre, him]

theorem haarForm_ind_ne_zero (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : haarForm μ (ind K hK) ≠ 0 := by
  have e : haarForm μ (ind K hK) = ∫ x, Set.indicator (K : Set G) (fun _ => (1 : ℂ)) x ∂μ := rfl
  rw [e, integral_indicator_const (1 : ℂ) K.isOpen.measurableSet]
  have h0 : μ (K : Set G) ≠ 0 := (K.isOpen.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have h1 : μ.real (K : Set G) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨h0, hK.measure_lt_top.ne⟩
  simpa using h1

end Integral

theorem exists_eq_mul_integral :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G],
      IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure] (L : SB G →ₗ[ℂ] ℂ),
      (∀ (g : G) (α : SB G), L (pullHomeo (Homeomorph.mulRight g) α) = L α) →
      ∃ c : ℂ, ∀ α : SB G, L α = c * ∫ x, (α : G → ℂ) x ∂μ := by
  intro G _ _ _ _ _ _ _ _ hU μ _ L hL
  obtain ⟨K₀, hK₀⟩ := GroundTheory.Automorphic.exists_compactOpenSubgroup (G := G)
  have hI := haarForm_right hU μ
  refine ⟨L (ind K₀ hK₀) / haarForm μ (ind K₀ hK₀), fun α => ?_⟩
  rw [← haarForm_apply]
  obtain ⟨K', hK'⟩ := exists_open_left_stab α.2
  have hKc : IsCompact ((K₀ ⊓ K' : OpenSubgroup G) : Set G) :=
    GroundTheory.Automorphic.isCompact_inf_left hK₀
  obtain ⟨s, hs⟩ := exists_coeff (K₀ ⊓ K') hKc α (fun k hk x => hK' k hk.2 x)
  obtain ⟨s₀, hs₀⟩ := exists_coeff (K₀ ⊓ K') hKc (ind K₀ hK₀)
    (fun k hk x => ind_left K₀ hK₀ hk.1 x)
  have hne := haarForm_ind_ne_zero μ (K₀ ⊓ K') hKc
  have hne₀ := haarForm_ind_ne_zero μ K₀ hK₀
  have h1 := hs L hL
  have h2 := hs _ hI
  have h3 := hs₀ L hL
  have h4 := hs₀ _ hI
  rw [h1, h2, h3, h4]
  have hs₀0 : s₀ ≠ 0 := fun h => hne₀ (by rw [h4, h, zero_mul])
  field_simp

end GlobalTheory.CompanionTheory.FrobHaarR
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralSplitColumn
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem measurePreserving_funUnique_symm {U : Type} [inst : Fintype U] [Unique U] :
    MeasurePreserving (MeasurableEquiv.funUnique U ℂ).symm (volume : Measure ℂ)
      (Measure.pi fun _ : U => (volume : Measure ℂ)) := by
  obtain rfl : inst = Unique.fintype := Subsingleton.elim _ _
  exact (measurePreserving_funUnique (volume : Measure ℂ) U).symm

theorem measurePreserving_joinEntry {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) :
    MeasurePreserving
      (fun p : ℂ × ({j : α // j ≠ j₀} → ℂ) =>
        (fun j => if h : j = j₀ then p.1 else p.2 ⟨j, h⟩ : α → ℂ))
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      (Measure.pi fun _ : α => (volume : Measure ℂ)) := by
  haveI : Unique {j : α // ¬ j ≠ j₀} :=
    { default := ⟨j₀, by simp⟩
      uniq := fun x => Subtype.ext (by simpa using x.2) }
  have h1 := (measurePreserving_piEquivPiSubtypeProd (fun _ : α => (volume : Measure ℂ))
    (fun j => j ≠ j₀)).symm
  have h2 : MeasurePreserving (MeasurableEquiv.funUnique {j : α // ¬ j ≠ j₀} ℂ).symm
      (volume : Measure ℂ) (Measure.pi fun _ : {j : α // ¬ j ≠ j₀} => (volume : Measure ℂ)) :=
    measurePreserving_funUnique_symm
  have h3 := (MeasurePreserving.id
    (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ))).prod h2
  have h4 : MeasurePreserving (Prod.swap : ℂ × ({j : α // j ≠ j₀} → ℂ) → _)
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      ((Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)).prod (volume : Measure ℂ)) :=
    Measure.measurePreserving_swap
  have h5 := h1.comp (h3.comp h4)
  convert h5 using 1
  funext p j
  by_cases h : j = j₀
  · subst h
    simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
  · simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, h]

theorem measurePreserving_joinCol (d : ℕ) {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) :
    MeasurePreserving
      (fun p : (Fin d → ℂ) × (Fin d → {j : α // j ≠ j₀} → ℂ) => joinCol j₀ p.1 p.2)
      volume volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow ℂ ({j : α // j ≠ j₀} → ℂ) (Fin d)).symm
  have h2 := measurePreserving_pi (fun _ : Fin d => (volume : Measure (ℂ × ({j : α // j ≠ j₀} → ℂ))))
    (fun _ : Fin d => (volume : Measure (α → ℂ))) (fun _ => measurePreserving_joinEntry j₀)
  exact h2.comp h1

theorem lintegral_joinCol : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (Φ : (Fin d → α → ℂ) → ℝ≥0∞), Measurable Φ → ∫⁻ C : Fin d → α → ℂ, Φ C = ∫⁻ C' : Fin d → {j : α // j ≠ j₀} → ℂ, ∫⁻ c : Fin d → ℂ, Φ (joinCol j₀ c C') := by
  intro d α _ _ j₀ Φ hΦ
  have hT := measurePreserving_joinCol d j₀
  rw [← hT.lintegral_comp hΦ]
  exact lintegral_prod_symm _ (hΦ.comp hT.measurable).aemeasurable

end GlobalTheory.CompanionTheory.FSCrofton
end

