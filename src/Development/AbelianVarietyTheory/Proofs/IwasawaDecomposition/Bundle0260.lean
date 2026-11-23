module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCardIndexRanks
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.GrpCount

section Count

variable {κ : Type} [CommRing κ] {r : ℕ}

theorem card_unitri (Fr : Fin r → Fin r → Prop) (hFr : ∀ i j, Fr i j → i < j) (H : Subgroup (GL (Fin r) κ))
    (hH : ∀ g : GL (Fin r) κ, g ∈ H ↔ (∀ i j, j < i → (g : Matrix (Fin r) (Fin r) κ) i j = 0) ∧
      (∀ i, (g : Matrix (Fin r) (Fin r) κ) i i = 1) ∧
      ∀ i j, i < j → ¬ Fr i j → (g : Matrix (Fin r) (Fin r) κ) i j = 0) :
    Nat.card H = Nat.card κ ^ Nat.card {p : Fin r × Fin r // Fr p.1 p.2} := by
  classical
  let mk : ({p : Fin r × Fin r // Fr p.1 p.2} → κ) → Matrix (Fin r) (Fin r) κ := fun f i j =>
    if i = j then 1 else if h : Fr i j then f ⟨(i, j), h⟩ else 0
  have hlow : ∀ f i j, j < i → mk f i j = 0 := by
    intro f i j hij
    have hne : i ≠ j := (ne_of_lt hij).symm
    simp only [mk, if_neg hne]
    rw [dif_neg]
    intro h
    exact absurd (hFr i j h) (not_lt.2 hij.le)
  have hdet : ∀ f, (mk f).det = 1 := by
    intro f
    rw [Matrix.det_of_upperTriangular (fun i j hij => hlow f i j hij)]
    simp [mk]
  let toG : ({p : Fin r × Fin r // Fr p.1 p.2} → κ) → GL (Fin r) κ := fun f =>
    Matrix.nonsingInvUnit (mk f) (by rw [hdet]; exact isUnit_one)
  have htoG : ∀ f, ((toG f : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) = mk f := fun f => rfl
  let e : H ≃ ({p : Fin r × Fin r // Fr p.1 p.2} → κ) :=
    { toFun := fun g p => (g.1 : Matrix (Fin r) (Fin r) κ) p.1.1 p.1.2
      invFun := fun f => ⟨toG f, (hH _).2 ⟨fun i j hij => by rw [htoG]; exact hlow f i j hij,
        fun i => by rw [htoG]; simp [mk],
        fun i j hij hn => by
          rw [htoG]
          simp only [mk, if_neg (ne_of_lt hij), dif_neg hn]⟩⟩
      left_inv := by
        intro g
        obtain ⟨h0, h1, h2⟩ := (hH g.1).1 g.2
        apply Subtype.ext
        apply Units.ext
        ext i j
        change mk (fun p => (g.1 : Matrix (Fin r) (Fin r) κ) p.1.1 p.1.2) i j = (g.1 : Matrix (Fin r) (Fin r) κ) i j
        simp only [mk]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, h1]
        · rw [if_neg hij]
          by_cases hf : Fr i j
          · rw [dif_pos hf]
          · rw [dif_neg hf]
            rcases lt_or_gt_of_ne hij with hl | hl
            · exact (h2 i j hl hf).symm
            · exact (h0 i j hl).symm
      right_inv := by
        intro f
        funext p
        show mk f p.1.1 p.1.2 = f p
        simp only [mk, if_neg (ne_of_lt (hFr _ _ p.2)), dif_pos p.2] }
  rw [Nat.card_congr e, Nat.card_fun]

theorem card_unip : Nat.card (unip κ r) = Nat.card κ ^ Nat.card {p : Fin r × Fin r // p.1 < p.2} := by
  refine card_unitri (fun i j => i < j) (fun _ _ h => h) _ fun g => ?_
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨fun i j hij => h0 hij, h1, fun i j hij hn => absurd hij hn⟩
  · rintro ⟨h0, h1, -⟩
    exact ⟨fun i j hij => h0 i j hij, h1⟩

theorem card_unipCol (a c : ℕ) : Nat.card (unipCol κ r a c) =
    Nat.card κ ^ Nat.card {p : Fin r × Fin r // p.1 < p.2 ∧ ¬ (a ≤ p.1.val ∧ p.1.val < c ∧ p.2.val = c)} := by
  refine card_unitri (fun i j => i < j ∧ ¬ (a ≤ i.val ∧ i.val < c ∧ j.val = c)) (fun _ _ h => h.1) _ fun g => ?_
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    refine ⟨fun i j hij => h0 hij, h1, fun i j hij hn => ?_⟩
    have : a ≤ i.val ∧ i.val < c ∧ j.val = c := by
      by_contra hc
      exact hn ⟨hij, hc⟩
    exact h2 i j this.1 this.2.1 this.2.2
  · rintro ⟨h0, h1, h2⟩
    refine ⟨⟨fun i j hij => h0 i j hij, h1⟩, fun i j ha hc hj => h2 i j ?_ ?_⟩
    · show i.val < j.val; omega
    · rintro ⟨-, hn⟩; exact hn ⟨ha, hc, hj⟩

theorem card_pairs_split {a c : ℕ} (hac : a ≤ c) (hc : c < r) :
    Nat.card {p : Fin r × Fin r // p.1 < p.2} =
      Nat.card {p : Fin r × Fin r // p.1 < p.2 ∧ ¬ (a ≤ p.1.val ∧ p.1.val < c ∧ p.2.val = c)} + (c - a) := by
  classical
  have hQ : Nat.card {p : Fin r × Fin r // p.1 < p.2 ∧ (a ≤ p.1.val ∧ p.1.val < c ∧ p.2.val = c)} = c - a := by
    rw [← Nat.card_fin (c - a)]
    refine Nat.card_congr
      { toFun := fun p => ⟨p.1.1.val - a, by have := p.2.2; omega⟩
        invFun := fun i => ⟨(⟨a + i.val, by have := i.2; omega⟩, ⟨c, hc⟩), by
          refine ⟨?_, ?_, ?_, rfl⟩
          · show a + i.val < c; have := i.2; omega
          · show a ≤ a + i.val; omega
          · show a + i.val < c; have := i.2; omega⟩
        left_inv := by
          rintro ⟨⟨i, j⟩, h1, h2, h3, h4⟩
          have h2' : a ≤ i.val := h2
          apply Subtype.ext
          apply Prod.ext
          · apply Fin.ext; show a + (i.val - a) = i.val; omega
          · apply Fin.ext; exact h4.symm
        right_inv := by
          intro i
          apply Fin.ext
          show a + i.val - a = i.val
          omega }
  rw [← hQ]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2))
    (fun p : Fin r × Fin r => a ≤ p.1.val ∧ p.1.val < c ∧ p.2.val = c), Finset.filter_filter, Finset.filter_filter,
    add_comm]

theorem card_pi {ι : Type} [Fintype ι] {M : ι → Type} [∀ i, Group (M i)] (H : ∀ i, Subgroup (M i)) :
    Nat.card (Subgroup.pi Set.univ H) = ∏ i, Nat.card (H i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr ((Equiv.subtypeEquivRight fun x => by simp [Subgroup.mem_pi]).trans
    (Equiv.subtypePiEquivPi (p := fun i y => y ∈ H i)))

end Count

end GlobalTheory.Mem.GrpCount

namespace GlobalTheory.Mem.GrpCount

theorem symPos_injective {r ρ k : ℕ} (h : ρ + k ≤ r) : Function.Injective (symPos r ρ k) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  simp only [symPos] at hv
  have hi := i.2
  have hj := j.2
  apply Fin.ext
  split_ifs at hv <;> rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv <;> omega

theorem index_of_lvlTie {D : D7} {G : Type} [Group G] {Q0 : Subgroup G} {ψ0 : Q0 →* D.what₂.LLˣ} {Qs : Subgroup G}
    {ψs : Qs →* D.what₂.LLˣ} {eG : G ≃* G0g D.nd} {Pg : Finset (Pl D.host.E)} {pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg}
    {res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)}
    {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} {eC : G ≃* G0 Pg D.R.r}
    (h : LvlTie D Q0 ψ0 Qs ψs eG Pg pl res ψ eC) :
    Nat.card Q0 = Nat.card Qs * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) := by
  have hrk : D.R.rS + D.R.k < D.R.r := by
    have := D.R.two_le_m
    simp only [Ranks.rS, Ranks.r]
    omega
  let σ : Fin D.R.r ≃ Fin D.R.r :=
    Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (symPos_injective hrk.le))
  have h0 : Nat.card Q0 = Nat.card (_root_.Formalism.L2.DIV.P0 Pg D.R.r ψ).H :=
    Nat.card_congr (eC.toEquiv.subtypeEquiv fun g => h.p0 g)
  let φ : G0 Pg D.R.r ≃ G0 Pg D.R.r := Equiv.piCongrRight fun PP =>
    (Units.mapEquiv (Matrix.reindexAlgEquiv (kP PP.1) (kP PP.1) σ.symm).toMulEquiv).toEquiv
  have hφ : ∀ (x : G0 Pg D.R.r) (PP : ↥Pg) (i j : Fin D.R.r),
      ((φ x PP : GL (Fin D.R.r) (kP PP.1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)) i j =
        ((x PP : GL (Fin D.R.r) (kP PP.1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1))
          (symPos D.R.r D.R.rS D.R.k i) (symPos D.R.r D.R.rS D.R.k j) := by
    intro x PP i j
    simp [φ, σ, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  have hs : Nat.card Qs = Nat.card (PsharpSym Pg D.R.r D.R.rS D.R.k ψ).H := by
    refine Nat.card_congr ((eC.toEquiv.trans φ).subtypeEquiv fun g => ?_)
    rw [h.ps g]
    constructor
    · rintro ⟨y, hy, hE⟩
      have hy' : φ (eC g) = y := by
        funext PP
        apply Units.ext
        ext i j
        rw [hφ]
        exact hE PP i j
      show φ (eC g) ∈ _
      rw [hy']
      exact hy
    · intro hm
      exact ⟨_, hm, fun PP i j => (hφ _ PP i j).symm⟩
  have hsplit := card_pairs_split (r := D.R.r) (a := D.R.rS) (c := D.R.rS + D.R.k) (by omega) hrk
  rw [Nat.add_sub_cancel_left] at hsplit
  have hP0 : Nat.card (_root_.Formalism.L2.DIV.P0 Pg D.R.r ψ).H =
      ∏ PP : ↥Pg, Nat.card (kP PP.1) ^ Nat.card {p : Fin D.R.r × Fin D.R.r // p.1 < p.2} := by
    show Nat.card (Subgroup.pi Set.univ fun PP : ↥Pg => unip (kP PP.1) D.R.r) = _
    rw [card_pi]
    exact Finset.prod_congr rfl fun PP _ => card_unip
  have hPs : Nat.card (PsharpSym Pg D.R.r D.R.rS D.R.k ψ).H =
      ∏ PP : ↥Pg, Nat.card (kP PP.1) ^ Nat.card {p : Fin D.R.r × Fin D.R.r //
        p.1 < p.2 ∧ ¬ (D.R.rS ≤ p.1.val ∧ p.1.val < D.R.rS + D.R.k ∧ p.2.val = D.R.rS + D.R.k)} := by
    show Nat.card (Subgroup.pi Set.univ fun PP : ↥Pg => unipCol (kP PP.1) D.R.r D.R.rS (D.R.rS + D.R.k)) = _
    rw [card_pi]
    exact Finset.prod_congr rfl fun PP _ => card_unipCol _ _
  have hk : ∏ PP : ↥Pg, Nat.card (kP PP.1) ^ D.R.k = (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) := by
    rw [← Equiv.prod_comp pl (fun PP : ↥Pg => Nat.card (kP PP.1) ^ D.R.k)]
    have hq : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Nat.card (kP (pl kv).1) = D.host.g kv.1 := fun kv => by
      rw [Nat.card_congr (res kv).toEquiv, Nat.card_zmod]
    simp only [hq]
    rw [Fintype.prod_sigma]
    simp only [Finset.prod_const, Finset.card_univ, D.nd.card_PlG, Fin.prod_univ_two]
    ring
  rw [h0, hs, hP0, hPs, ← hk, hsplit, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun PP _ => pow_add _ _ _

end GlobalTheory.Mem.GrpCount

namespace GlobalTheory.Mem.R3

theorem pins_card_index_ranks : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type)
    (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG →
    Fintype.card G = D.what₂.restRowsFiniteGroupCard ∧ Nat.card F.P0 = Nat.card F.P1 * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) ∧
      A3.A.r = D.R.r ∧ A3.A.t = D.R.t ∧ A3.A.v0 = InfinitePlace.mk D.what₂.embLL := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG h
  obtain ⟨gramR, c0R, c0L, hT⟩ := h.char.base.fam.tie
  refine ⟨?_, ?_, hT.ranks.2.1, hT.ranks.2.2, hT.v0⟩
  · rw [← Nat.card_eq_fintype_card, Nat.card_congr (R.eG.trans cG).toEquiv, D.nd.restN_card_levelGroup_eq, Nat.card_pi,
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change ∏ _y : D.nd.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) = _
    rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG k]
  · obtain ⟨Pg, pl, res, ψ, eC, hL, -⟩ := h.keep.psi
    exact GlobalTheory.Mem.GrpCount.index_of_lvlTie hL

end GlobalTheory.Mem.R3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointCarriesFrameFlagsTransferBetweenFlagBundles
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle.Transfer

variable {ι : Type} {m : ι → ℕ}

theorem inv_mul_cancel_left {K : Type} [Field K] {g : Mat m K} (hg : ∀ τ, (g τ).det ≠ 0) (X : Mat m K) :
    g⁻¹ * (g * X) = X := by
  rw [← mul_assoc, Mat.inv_mul hg, one_mul]

theorem mul_inv_cancel_left {K : Type} [Field K] {g : Mat m K} (hg : ∀ τ, (g τ).det ≠ 0) (X : Mat m K) :
    g * (g⁻¹ * X) = X := by
  rw [← mul_assoc, Mat.mul_inv hg, one_mul]

theorem det_mul_ne {K : Type} [Field K] {g g' : Mat m K} (hg : ∀ τ, (g τ).det ≠ 0) (hg' : ∀ τ, (g' τ).det ≠ 0)
    (τ : ι) : ((g * g') τ).det ≠ 0 := by
  rw [Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hg τ) (hg' τ)

theorem par_of_three {K : Type} [Field K] {k : ι → ℕ} {h h' P Q E L : Mat m K} (hP : ∀ τ, (P τ).det ≠ 0)
    (hQ : ∀ τ, (Q τ).det ≠ 0) (hE : ∀ τ, (E τ).det ≠ 0) (hL : Par k ⊤ L) (G1 : Par k ⊤ (h * P⁻¹))
    (G2 : Par k ⊤ (h' * (L * (P * E))⁻¹)) (G3 : Par k ⊤ (h' * (Q * E)⁻¹)) : Par k ⊤ (h * Q⁻¹) := by
  have hh' : ∀ τ, (h' τ).det ≠ 0 := fun τ => by
    have := G3.det_ne τ
    rw [Pi.mul_apply, Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  have hLPE : ∀ τ, ((L * (P * E)) τ).det ≠ 0 := det_mul_ne hL.det_ne (det_mul_ne hP hE)
  have e : h * Q⁻¹ = h * P⁻¹ * L⁻¹ * (h' * (L * (P * E))⁻¹)⁻¹ * (h' * (Q * E)⁻¹) := by
    rw [Mat.mul_inv_rev h', Mat.inv_inv hLPE, Mat.mul_inv_rev Q E]
    simp only [mul_assoc]
    rw [inv_mul_cancel_left hh', mul_inv_cancel_left hE, inv_mul_cancel_left hL.det_ne,
      inv_mul_cancel_left hP]
  rw [e]
  exact ((G1.mul hL.inv).mul G2.inv).mul G3

variable {F : Type} [Field F]

theorem sp_specializes {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) (w : Sp K) :
    p w ⤳ p (IsLocalRing.closedPoint K) := by
  rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]

theorem val_map_mul {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) {k k' : ι → ℕ} {g g' : Mat m Y.Fn}
    (hg : Par k ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring g)
    (hg' : Par k' ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring g') :
    (g * g').map ((ratOf Y).val p) = g.map ((ratOf Y).val p) * g'.map ((ratOf Y).val p) :=
  hg.map_mul_of hg' _ (RatModel.valHomOf p _ (sp_specializes p)) fun _ => rfl

theorem val_map_par {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) {k : ι → ℕ} {g : Mat m Y.Fn}
    (hg : Par k ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring g) :
    Par k ⊤ (g.map ((ratOf Y).val p)) :=
  hg.map_of _ (RatModel.valHomOf p _ (sp_specializes p)) fun _ => rfl

theorem frame_change {X Y : Var F} (ψ : X.Fn →ₐ[F] Y.Fn) (A B : Mat m X.Fn) (hA : ∀ τ, (A τ).det ≠ 0)
    : ∀ C : Mat m Y.Fn, C * (B.map ψ)⁻¹ = (C * (A.map ψ)⁻¹) * (A * B⁻¹).map ψ := by
  intro C
  have hA' : ∀ τ, ((A.map ψ) τ).det ≠ 0 := fun τ => by
    have e : (A.map ψ τ).det = ψ (A τ).det := Mat.det_map A ψ.toRingHom τ
    rw [e]; exact (map_ne_zero _).2 (hA τ)
  have e1 : (A * B⁻¹).map ψ = A.map ψ * B⁻¹.map ψ := Mat.map_mul A B⁻¹ ψ.toRingHom
  have e2 : B⁻¹.map ψ = (B.map ψ)⁻¹ := Mat.map_inv B ψ.toRingHom
  rw [e1, e2]
  show C * (B.map ψ)⁻¹ = C * (A.map ψ)⁻¹ * (A.map ψ * (B.map ψ)⁻¹)
  rw [mul_assoc, inv_mul_cancel_left hA']

theorem val_map_hom {X Y : Var F} {ψ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : (ratOf X).IsHom (ratOf Y) ψ f)
    {K : Type} [Field K] (p : Sp K ⟶ Y.X) {k : ι → ℕ} {D : Mat m X.Fn}
    (hD : Par k ((ratOf X).O (f (p (IsLocalRing.closedPoint K)))).toSubring D) :
    (D.map ψ).map ((ratOf Y).val p) = D.map ((ratOf X).val (p ≫ f)) := by
  funext τ
  ext i j
  exact (hf.val_comp p (IsLocalRing.closedPoint K) ((hD τ).1 i j)).symm

theorem par_map_hom {X Y : Var F} {ψ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : (ratOf X).IsHom (ratOf Y) ψ f)
    {z : Y.X} {k : ι → ℕ} {D : Mat m X.Fn} (hD : Par k ((ratOf X).O (f z)).toSubring D) :
    Par k ((ratOf Y).O z).toSubring (D.map ψ) :=
  hD.map ψ.toRingHom fun _ hx => hf.map_mem_O hx

end GlobalTheory.FlagBundle.Transfer

namespace GlobalTheory.FlagBundle

open Transfer

theorem Bears.transfer : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F)
    (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ →
    ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ →
    ∀ A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)), ∀ B ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)),
    ∀ h h' : Mat m K, Bears S₁ φ₁ A h p → Bears S₁ φ₁ B h' p → Bears S₂ φ₂ B h' q → Bears S₂ φ₂ A h q := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ R₁ R₂ K _ p q hpq A hA B hB h h' b1 b2 b3
  obtain ⟨A₁, hA₁, G1⟩ := b1
  obtain ⟨A₁', hA₁', G2⟩ := b2
  obtain ⟨A₂, hA₂, G3⟩ := b3
  refine ⟨A₂, hA₂, ?_⟩
  have hx1 : f₁ (p (IsLocalRing.closedPoint K)) = (p ≫ f₁) (IsLocalRing.closedPoint K) := rfl
  have hx2 : f₂ (q (IsLocalRing.closedPoint K)) = (p ≫ f₁) (IsLocalRing.closedPoint K) := by rw [hpq]; rfl
  have hD : Par 0 ((ratOf X).O ((p ≫ f₁) (IsLocalRing.closedPoint K))).toSubring (A * B⁻¹) := (Fr.mem_iff hB).1 hA
  have hD1 : Par 0 ((ratOf X).O (f₁ (p (IsLocalRing.closedPoint K)))).toSubring (A * B⁻¹) := hx1 ▸ hD
  have hD2 : Par 0 ((ratOf X).O (f₂ (q (IsLocalRing.closedPoint K)))).toSubring (A * B⁻¹) := hx2 ▸ hD
  have C1 := R₁.2.1 _ A₁ hA₁ A (hx1 ▸ hA)
  have C1B := R₁.2.1 _ A₁ hA₁ B (hx1 ▸ hB)
  have C2 := R₂.2.1 _ A₂ hA₂ A (hx2 ▸ hA)
  have L1 := (Fr.mem_iff hA₁).1 hA₁'
  have e1 : A₁' * (B.map φ₁)⁻¹ = (A₁' * A₁⁻¹) * (A₁ * (B.map φ₁)⁻¹) := by
    rw [mul_assoc, inv_mul_cancel_left (Fr.det_ne hA₁)]
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  rw [e1, val_map_mul p L1 C1B, frame_change φ₁ A B hAd, val_map_mul p C1 (par_map_hom R₁.1 hD1),
    val_map_hom R₁.1 p hD1] at G2
  rw [frame_change φ₂ A B hAd, val_map_mul q C2 (par_map_hom R₂.1 hD2), val_map_hom R₂.1 q hD2] at G3
  have ev : (A * B⁻¹).map ((ratOf X).val (q ≫ f₂)) = (A * B⁻¹).map ((ratOf X).val (p ≫ f₁)) :=
    congrArg (fun y => (A * B⁻¹).map ((ratOf X).val y)) hpq.symm
  rw [ev] at G3
  have hE : Par 0 ⊤ ((A * B⁻¹).map ((ratOf X).val (p ≫ f₁))) := by
    rw [← val_map_hom R₁.1 p hD1]; exact val_map_par p (par_map_hom R₁.1 hD1)
  exact par_of_three (val_map_par p C1).det_ne (val_map_par q C2).det_ne hE.det_ne (val_map_par p L1) G1 G2 G3

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RangeEEAndNorm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.RowsLvl

section Scale

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isMultiplicityInner_smul_measure (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {c : ℝ}
    (hc : 0 < c) {k : ℂ} (h : IsMultIP M μ 𝓕 T T' k) :
    IsMultIP M (ENNReal.ofReal c • μ) 𝓕 T T' ((c : ℂ) * k) := by
  intro v v'
  obtain ⟨hi, he⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at hi ⊢
    rw [Measure.restrict_smul]
    exact hi.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, he, ENNReal.toReal_ofReal hc.le, Complex.real_smul, mul_assoc]

theorem ipM_smul (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {c : ℝ}
    (hc : 0 < c) (hv : ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) :
    ipM M (ENNReal.ofReal c • μ) 𝓕 T T' = (c : ℂ) * ipM M μ 𝓕 T T' := by
  obtain ⟨v, hv⟩ := hv
  by_cases h : ∃ k, IsMultIP M μ 𝓕 T T' k
  · have hs := isMultiplicityInner_smul_measure M μ 𝓕 T T' hc (ipM_spec M μ 𝓕 T T' h)
    exact hasPeterssonInner_unique M _ 𝓕 T T' v hv (ipM_spec M _ 𝓕 T T' ⟨_, hs⟩) hs
  · have h' : ¬ ∃ k, IsMultIP M (ENNReal.ofReal c • μ) 𝓕 T T' k := by
      rintro ⟨k, hk⟩
      have e : ENNReal.ofReal c⁻¹ • ENNReal.ofReal c • μ = μ := by
        rw [smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one, one_smul]
      have := isMultiplicityInner_smul_measure M _ 𝓕 T T' (inv_pos.2 hc) hk
      rw [e] at this
      exact h ⟨_, this⟩
    unfold ipM
    rw [dite_eq_right h, dite_eq_right h', mul_zero]

theorem mmap_eq_zero (M : DSModel V S) (hv : ¬ ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) (T : MMap M) :
    T = 0 := by
  classical
  have : ∃ τ, ∀ w : M.sm τ, w = 0 := by
    by_contra hne
    push_neg at hne
    choose w hw using hne
    refine hv ⟨w, Finset.prod_ne_zero_iff.2 fun τ _ => ?_⟩
    rw [inner_self_ne_zero]
    exact fun h0 => hw τ (Subtype.ext h0)
  obtain ⟨τ, hτ⟩ := this
  ext v g
  rw [T.map_coord_zero τ (hτ (v τ))]
  rfl

end Scale

end GlobalTheory.Mem.R3.RowsLvl

namespace GlobalTheory.Mem.R3.RowsLvl


set_option maxHeartbeats 2000000 in
theorem range_eE_and_norm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → LinearMap.range Y.eE = (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).comap R.HE.e ∧ ∀ x, ‖Y.eE x‖ ^ 2 = RealDat.nP F.lv2 true * ‖x‖ ^ 2 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _
  have hE : R.models_HE := hP.char.base.models.HE
  have hEEc : (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).EEc true =
      (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).map
        (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap := rfl
  have hlift : Function.Injective (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) :=
    LinearEquiv.injective _
  refine ⟨?_, fun x => ?_⟩
  · ext h
    constructor
    · rintro ⟨x, rfl⟩
      have hm := (Y.Ish.jE x).2
      rw [Y.eE_read, hEEc] at hm
      obtain ⟨u, hu, he⟩ := hm
      have : u = R.HE.e (Y.eE x) := hlift he
      rw [Submodule.mem_comap, ← this]
      exact hu
    · intro hh
      rw [Submodule.mem_comap] at hh
      have hm : (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) (R.HE.e h) ∈
          (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).EEc true := by
        rw [hEEc]; exact ⟨_, hh, rfl⟩
      refine ⟨Y.Ish.jE.symm ⟨_, hm⟩, ?_⟩
      have e1 := Y.eE_read (Y.Ish.jE.symm ⟨_, hm⟩)
      rw [LinearEquiv.apply_symm_apply] at e1
      exact (hE.1 (hlift e1)).symm
  · have hx := Y.tied.sharp.ee x x
    have hy := hE.2.2 (Y.eE x) (Y.eE x)
    have hnP : 0 < RealDat.nP F.lv2 true := by
      unfold RealDat.nP; exact_mod_cast Nat.card_pos
    by_cases hv : ∃ v : (R.MY 0).Vec, ∏ τ, ⟪(v τ : (R.MY 0).H τ), (v τ : (R.MY 0).H τ)⟫_ℂ ≠ 0
    · have e : ⟪x, x⟫_ℂ = (((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) * ⟪Y.eE x, Y.eE x⟫_ℂ := by
        rw [hx, hy]
        show ipMT _ _ _ _ _ = _
        unfold ipMT
        rw [Y.eE_read]
        erw [LinearEquiv.symm_apply_apply]
        exact ipM_smul _ _ _ _ _ (inv_pos.2 hnP) hv
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e
      have e' : ‖x‖ ^ 2 = (RealDat.nP F.lv2 true)⁻¹ * ‖Y.eE x‖ ^ 2 := by
        apply Complex.ofReal_injective
        rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
        exact e
      rw [e', ← mul_assoc, mul_inv_cancel₀ hnP.ne', one_mul]
    · have h0 : Y.eE x = 0 :=
        hE.1 (by rw [mmap_eq_zero _ hv (R.HE.e (Y.eE x)), mmap_eq_zero _ hv (R.HE.e 0)])
      have h1 : (Y.Ish.jE x).1 = 0 := by
        rw [Y.eE_read, h0, map_zero]; exact map_zero _
      have hx0 : x = 0 := (LinearEquiv.map_eq_zero_iff _).1 (Submodule.coe_eq_zero.1 h1)
      simp [h0, hx0]

end GlobalTheory.Mem.R3.RowsLvl
end
end

