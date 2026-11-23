module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceTypePrimeDescription
section
namespace IteratedIwahori
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.IterJ

section Gen
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem intM_submatrix_iff (e : a ≃ b) (M : Matrix a a k) :
    GlobalTheory.StepData.IntM (M.submatrix e.symm e.symm) ↔ GlobalTheory.StepData.IntM M :=
  ⟨fun h i j => by simpa using h (e i) (e j), fun h _ _ => h _ _⟩

theorem reGL_mem_KO_iff (e : a ≃ b) (g : GL a k) : reGL e g ∈ KO k b ↔ g ∈ KO k a := by
  rw [GlobalTheory.StepData.mem_KO, GlobalTheory.StepData.mem_KO, ← map_inv, reGL_val, reGL_val,
    intM_submatrix_iff, intM_submatrix_iff]


omit [Fintype a] [Fintype b] [DecidableEq b] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem symm_sub_one_apply [Fintype a] [Fintype b] [DecidableEq b] (e : a ≃ b) (h : GL b k) (x y : a) :
    (((reGL e).symm h).val - 1) x y = (h.val - 1) (e x) (e y) := by
  simp [reGL_symm_val, Matrix.one_apply]

end Gen

section Iter
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

theorem blk_le {j : ℕ} (x : Ix r t j) : Ix.blk x ≤ j := by
  rcases x with x | ⟨c, s⟩
  · simp [Ix.blk]
  · simpa [Ix.blk] using c.2

theorem blk_ixSucc_inl {j : ℕ} (x : Ix r t j) : Ix.blk (ixSucc r t j (Sum.inl x)) = Ix.blk x := by
  rcases x with x | ⟨c, s⟩ <;> simp [Ix.blk, ixSucc]

theorem blk_ixSucc_inr {j : ℕ} (s : t) : Ix.blk (ixSucc r t j (Sum.inr s)) = j + 1 := by
  simp [Ix.blk, ixSucc]

theorem mem_iter_J (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (h : GL (Ix r t j) k) :
    h ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ h ∈ KO k (Ix r t j) ∧
      (∀ a b, Ix.blk b < Ix.blk a → valuation k (h.val a b) < 1) ∧
      ∀ a b : r, valuation k ((h.val - 1) (Sum.inl a) (Sum.inl b)) < 1 := by
  induction j with
  | zero =>
    rw [TypeDatum.iter_zero]
    have hK : (reGL (ixZero r t)).symm h ∈ KO k r ↔ h ∈ KO k (Ix r t 0) := by
      rw [← reGL_mem_KO_iff (ixZero r t), MulEquiv.apply_symm_apply]
    have mem : h ∈ ((TypeDatum.principal k r).reindex (ixZero r t)).J ↔
      (reGL (ixZero r t)).symm h ∈ KOne k r := Iff.rfl
    rw [mem, GlobalTheory.StepData.mem_KOne]
    constructor
    · intro hh
      refine ⟨hK.1 (GlobalTheory.StepData.KOne_le_KO (GlobalTheory.StepData.mem_KOne.2 hh)), fun a b hab => ?_, fun a b => ?_⟩
      · rcases a with a | ⟨c, _⟩
        · simp [Ix.blk] at hab
        · exact c.elim0
      · have := hh a b
        rwa [symm_sub_one_apply] at this
    · rintro ⟨-, -, h3⟩ a b
      rw [symm_sub_one_apply]
      exact h3 a b
  | succ j ih =>
    rw [TypeDatum.iter_succ]
    have hK : (reGL (ixSucc r t j)).symm h ∈ KO k (Ix r t j ⊕ t) ↔ h ∈ KO k (Ix r t (j + 1)) := by
      rw [← reGL_mem_KO_iff (ixSucc r t j), MulEquiv.apply_symm_apply]
    have mem : h ∈ ((((TypeDatum.principal k r).iter t μ hμ j).step t (μ (j + 1)) (hμ _)).reindex (ixSucc r t j)).J ↔
      (reGL (ixSucc r t j)).symm h ∈ ((TypeDatum.principal k r).iter t μ hμ j).stepJ t := Iff.rfl
    have ent : ∀ x y, ((reGL (ixSucc r t j)).symm h).val x y = h.val (ixSucc r t j x) (ixSucc r t j y) := fun _ _ => rfl
    rw [mem, TypeDatum.mem_stepJ_iff]
    constructor
    · rintro ⟨h0, ⟨g, hg, eg⟩, hC⟩
      obtain ⟨-, g2, g3⟩ := (ih g).1 hg
      have eg' : ∀ x y, g.val x y = h.val (ixSucc r t j (Sum.inl x)) (ixSucc r t j (Sum.inl y)) := fun x y => by
        rw [eg]; rfl
      refine ⟨hK.1 h0, fun a b hab => ?_, fun a b => ?_⟩
      · obtain ⟨x, rfl⟩ := (ixSucc r t j).surjective a
        obtain ⟨y, rfl⟩ := (ixSucc r t j).surjective b
        rcases x with x | s <;> rcases y with y | s'
        · rw [blk_ixSucc_inl, blk_ixSucc_inl] at hab
          rw [← eg']
          exact g2 x y hab
        · rw [blk_ixSucc_inl, blk_ixSucc_inr] at hab
          have := blk_le x
          omega
        · have := hC s y
          rwa [toBlocks₂₁, Matrix.of_apply, ent] at this
        · rw [blk_ixSucc_inr, blk_ixSucc_inr] at hab
          omega
      · have := g3 a b
        have e1 : ∀ c : r, (Sum.inl c : Ix r t (j + 1)) = ixSucc r t j (Sum.inl (Sum.inl c)) := fun c => rfl
        rw [e1 a, e1 b, ← symm_sub_one_apply, Matrix.sub_apply, ent]
        rw [Matrix.sub_apply, eg'] at this
        simpa [Matrix.one_apply] using this
    · rintro ⟨h1, h2, h3⟩
      have h0 := hK.2 h1
      have hC : GlobalTheory.StepData.MaxM ((reGL (ixSucc r t j)).symm h).val.toBlocks₂₁ := fun s y => by
        rw [toBlocks₂₁, Matrix.of_apply, ent]
        refine h2 _ _ ?_
        rw [blk_ixSucc_inl, blk_ixSucc_inr]
        have := blk_le y
        omega
      obtain ⟨⟨g, hg, eg⟩, -⟩ := GlobalTheory.StepData.exists_diag_blocks h0 hC
      have eg' : ∀ x y, g.val x y = h.val (ixSucc r t j (Sum.inl x)) (ixSucc r t j (Sum.inl y)) := fun x y => by
        rw [eg]; rfl
      refine ⟨h0, ⟨g, (ih g).2 ⟨hg, fun a b hab => ?_, fun a b => ?_⟩, eg⟩, hC⟩
      · rw [eg']
        refine h2 _ _ ?_
        rwa [blk_ixSucc_inl, blk_ixSucc_inl]
      · have := h3 a b
        have e1 : ∀ c : r, (Sum.inl c : Ix r t (j + 1)) = ixSucc r t j (Sum.inl (Sum.inl c)) := fun c => rfl
        rw [e1 a, e1 b, ← symm_sub_one_apply, Matrix.sub_apply, ent] at this
        rw [Matrix.sub_apply, eg']
        simpa [Matrix.one_apply] using this

end Iter

theorem blkOf_ixFin {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (j : ℕ)
    (x : Ix (Fin D.R.r) (Fin D.R.t) j) :
    Formalism.L2.DIV.blkOf D.R.r D.R.t (ixFin G t w j x) = Ix.blk x := by
  obtain ⟨h1, h2⟩ := ixFin_val G t w j
  rcases x with a | ⟨c, b⟩
  · simp [Formalism.L2.DIV.blkOf, h1, Ix.blk]
  · have hb := b.2
    have hpos : 0 < D.R.t := by omega
    have hdiv : (b.val + D.R.t * c.val) / D.R.t = c.val := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hb, zero_add]
    simp [Formalism.L2.DIV.blkOf, h2, Ix.blk, hdiv]

theorem mem_stepGroup_map_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∈ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (∀ a b, Formalism.L2.DIV.blkOf D.R.r D.R.t b < Formalism.L2.DIV.blkOf D.R.r D.R.t a → valuation (Kw w) (g.1 a b) < 1) ∧ ∀ a b : Fin ((locGrid G t w).rank (0, j)), a.val < D.R.r → b.val < D.R.r → valuation (Kw w) ((g.1 - 1) a b) < 1 := by
  intro D T L sc G t w hw j g
  have hmap : g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔
      (reGL (ixFin G t w j)).symm g ∈ stepGroup L t w j := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hx
      exact ⟨_, hx, by simp⟩
  have hK : (reGL (ixFin G t w j)).symm g ∈ KO (Kw w) (Ix (Fin D.R.r) (Fin D.R.t) j) ↔
      g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) := by
    rw [← reGL_mem_KO_iff (ixFin G t w j), MulEquiv.apply_symm_apply]
  rw [hmap, stepGroup, if_pos hw, mem_iter_J, hK]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · constructor
    · intro h a b hab
      obtain ⟨x, rfl⟩ := (ixFin G t w j).surjective a
      obtain ⟨y, rfl⟩ := (ixFin G t w j).surjective b
      rw [blkOf_ixFin, blkOf_ixFin] at hab
      exact h x y hab
    · intro h x y hxy
      refine h _ _ ?_
      rwa [blkOf_ixFin, blkOf_ixFin]
  · obtain ⟨h1, -⟩ := ixFin_val G t w j
    constructor
    · intro h a b ha hb
      have e : ∀ (c : Fin ((locGrid G t w).rank (0, j))) (hc : c.val < D.R.r),
          ixFin G t w j (Sum.inl ⟨c.val, hc⟩) = c := fun c hc => Fin.ext (h1 _)
      have := h ⟨a.val, ha⟩ ⟨b.val, hb⟩
      rwa [symm_sub_one_apply, e, e] at this
    · intro h a b
      rw [symm_sub_one_apply]
      exact h _ _ (by rw [h1]; exact a.2) (by rw [h1]; exact b.2)

end GlobalTheory.CompanionTheory.IterJ

end
end

end IteratedIwahori
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∈ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (∀ a b, Formalism.L2.DIV.blkOf D.R.r D.R.t b < Formalism.L2.DIV.blkOf D.R.r D.R.t a → valuation (Kw w) (g.1 a b) < 1) ∧ ∀ a b : Fin ((locGrid G t w).rank (0, j)), a.val < D.R.r → b.val < D.R.r → valuation (Kw w) ((g.1 - 1) a b) < 1 := by
  first | exact @IteratedIwahori.GlobalTheory.CompanionTheory.IterJ.mem_stepGroup_map_iff | exact IteratedIwahori.GlobalTheory.CompanionTheory.IterJ.mem_stepGroup_map_iff | (intros; apply IteratedIwahori.GlobalTheory.CompanionTheory.IterJ.mem_stepGroup_map_iff <;> assumption)

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToLinTransposeDot
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DualDatumDot

def dotL {O : Type} [CommRing O] {h : ℕ} (u : Fin h → O) : (Fin h → O) →ₗ[O] O where
  toFun m := u ⬝ᵥ m
  map_add' a b := dotProduct_add u a b
  map_smul' c m := by simp

theorem dot_single {O : Type} [CommRing O] {h : ℕ} (g : (Fin h → O) →ₗ[O] O) (x : Fin h → O) :
    (fun i => g (Pi.single i 1)) ⬝ᵥ x = g x := by
  have hx : x = ∑ i, x i • Pi.single i (1 : O) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, dotProduct, mul_comm]

theorem toLin'_transpose_dot {A O : Type} [CommRing A] [CommRing O] (θ : A →+* O) {h : ℕ}
    (X : Matrix (Fin h) (Fin h) A) (a b : Fin h → O) :
    Matrix.toLin' (Xᵀ.map θ) a ⬝ᵥ b = a ⬝ᵥ Matrix.toLin' (X.map θ) b := by
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.transpose_map, Matrix.mulVec_transpose,
    Matrix.dotProduct_mulVec]

end GlobalTheory.DualDatumDot

open GlobalTheory.DualDatumDot

namespace GlobalTheory.DualDatum

theorem hasDatum_dual : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → HasDatum hε G.dual := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G ⟨D, e, fil, lie, hA, hB⟩
  have hζ : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  obtain ⟨hdom, -, -, -, hν, hξ, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hζ
  have hν' : nu ε ≠ 0 := fun h0 => hν (by rw [h0, map_zero])
  have hμ : Sandwich.mu ε ≠ 0 := by rw [← xi_mul_nu]; exact mul_ne_zero hξ hν'
  obtain ⟨-, h1, -, h3, -⟩ := HodgeTateBound.bound p C v O hv ε hζ ℤ_[p] _ D
  have := hv.isFractionRing
  have := hv.isIntegrallyClosed
  have : IsIntegrallyClosedIn O C :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn C).1 inferInstance
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G
  haveI := hfin
  haveI := hproj
  let θ := WittVector.fontaineTheta O p
  let D' := SelfDualFil.dualDatum hμ hξ D

  have perp : ∀ a, a ∈ D'.Fil ↔ ∀ f ∈ D.Fil, a ⬝ᵥ f = 0 := by
    intro a
    change Matrix.toLin' ((D.F)ᵀ.map θ) a = 0 ↔ _
    constructor
    · intro ha f hf
      obtain ⟨w, hw⟩ := h3 f hf
      have e1 : a ⬝ᵥ D.al w = 0 := by
        rw [show D.al w = Matrix.toLin' (D.F.map θ) w from rfl, ← toLin'_transpose_dot, ha,
          zero_dotProduct]
      rw [hw, dotProduct_smul, smul_eq_mul] at e1
      exact (mul_eq_zero.1 e1).resolve_left hν
    · intro ha
      funext i
      have h2 := ha _ (h1 ⟨Pi.single i 1, rfl⟩)
      rw [show D.al (Pi.single i 1) = Matrix.toLin' (D.F.map θ) (Pi.single i 1) from rfl,
        ← toLin'_transpose_dot] at h2
      simpa using h2

  let E : Fin G.height → G.Tate := fun i => e.symm (Pi.single i 1)
  have hexp : ∀ t, t = ∑ i, e t i • E i := by
    intro t
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    ext j
    simp [E, Finset.sum_apply, Pi.single_apply]
  let L : G.dual.Tate →ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) :=
    LinearMap.pi fun i => (epsEquiv hε).symm.toLinearMap ∘ₗ pairing G O (E i)
  have hL : ∀ χ i, L χ i = epsPairing hε G (E i) χ := fun _ _ => rfl
  have hflip := G.pairing_flip_bijective C
  have hLb : Function.Bijective L := by
    constructor
    · refine (injective_iff_map_eq_zero L).2 fun χ hχ => hflip.1 ?_
      rw [map_zero]
      refine LinearMap.ext fun t => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LinearMap.flip_apply, LinearMap.zero_apply, hexp t, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, LinearMap.smul_apply, ← epsPairing_smul hε, ← hL, hχ]
      simp
    · intro c
      let φ : G.Tate →ₗ[ℤ_[p]] (PDivGroup.mu p O).Tate :=
        (epsEquiv hε).toLinearMap ∘ₗ (∑ i, c i • LinearMap.proj i) ∘ₗ e.toLinearMap
      obtain ⟨χ, hχ⟩ := hflip.2 φ
      refine ⟨χ, funext fun j => ?_⟩
      have hj : pairing G O (E j) χ = φ (E j) := LinearMap.congr_fun hχ (E j)
      rw [hL, epsPairing, hj]
      simp [φ, E, Pi.single_apply]
  let e' : G.dual.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) := LinearEquiv.ofBijective L hLb
  have he' : ∀ χ i, e' χ i = epsPairing hε G (E i) χ := fun _ _ => rfl
  have hdualb : ∀ t i, epsPairing hε G t (e'.symm (Pi.single i 1)) = e t i := by
    intro t i
    have hj : ∀ j, epsPairing hε G (E j) (e'.symm (Pi.single i 1)) = (Pi.single i (1 : ℤ_[p]) : Fin G.height → ℤ_[p]) j := by
      intro j
      rw [← he', LinearEquiv.apply_symm_apply]
    have hs : ∀ s, epsPairing hε G s (e'.symm (Pi.single i 1)) =
        (epsEquiv hε).symm.toLinearMap ((pairing G O).flip (e'.symm (Pi.single i 1)) s) :=
      fun _ => rfl
    rw [hs]
    conv_lhs => rw [hexp t]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    simp only [map_smul, ← hs, hj, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

  let Φ : G.omega →ₗ[O] (Fin G.height → O) :=
    LinearMap.pi fun i => lie (D.Fil.mkQ (Pi.single i 1))
  let g : G.omega → (Fin G.height → O) →ₗ[O] O := fun w =>
    Module.Dual.eval O G.omega w ∘ₗ lie.toLinearMap ∘ₗ D.Fil.mkQ
  have hΦdot : ∀ w m, Φ w ⬝ᵥ m = lie (D.Fil.mkQ m) w := fun w m => dot_single (g w) m
  have hΦmem : ∀ w, Φ w ∈ D'.Fil := fun w => (perp _).2 fun f hf => by
    rw [hΦdot, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hf, map_zero,
      LinearMap.zero_apply]
  have hΦinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun w hw => ?_
    apply (Module.evalEquiv O G.omega).injective
    rw [map_zero]
    refine LinearMap.ext fun x => ?_
    obtain ⟨q, rfl⟩ := lie.surjective x
    obtain ⟨m, rfl⟩ := D.Fil.mkQ_surjective q
    rw [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearMap.zero_apply, ← hΦdot, hw,
      zero_dotProduct]
  have hΦsurj : ∀ u ∈ D'.Fil, ∃ w, Φ w = u := by
    intro u hu
    have hle : D.Fil ≤ LinearMap.ker (dotL u) := fun f hf => (perp u).1 hu f hf
    let ℓ : G.Lie →ₗ[O] O := D.Fil.liftQ (dotL u) hle ∘ₗ lie.symm.toLinearMap
    refine ⟨(Module.evalEquiv O G.omega).symm ℓ, funext fun i => ?_⟩
    have hw : ∀ x : G.Lie, x ((Module.evalEquiv O G.omega).symm ℓ) = ℓ x := fun x => by
      have h5 := LinearMap.congr_fun ((Module.evalEquiv O G.omega).apply_symm_apply ℓ) x
      rwa [Module.evalEquiv_apply, Module.Dual.eval_apply] at h5
    change lie (D.Fil.mkQ (Pi.single i 1)) _ = u i
    rw [hw]
    change D.Fil.liftQ (dotL u) hle (lie.symm (lie (D.Fil.mkQ (Pi.single i 1)))) = u i
    rw [LinearEquiv.symm_apply_apply]
    change u ⬝ᵥ Pi.single i 1 = u i
    simp
  let filE : G.omega ≃ₗ[O] D'.Fil := LinearEquiv.ofBijective (Φ.codRestrict D'.Fil hΦmem)
    ⟨fun a b hab => hΦinj (congrArg Subtype.val hab), fun u => by
      obtain ⟨w, hw⟩ := hΦsurj u.1 u.2
      exact ⟨w, Subtype.ext hw⟩⟩
  let fil' : G.dual.dual.omega ≃ₗ[O] D'.Fil := (DlogSpan.pDivGroupOmegaBidualEquiv G).symm ≪≫ₗ filE

  let Ψ : (Fin G.height → O) →ₗ[O] G.dual.Lie :=
    LinearMap.mk₂ O (fun m w => m ⬝ᵥ (fil w : Fin G.height → O))
      (fun _ _ _ => by simp [add_dotProduct]) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp [dotProduct_add]) (fun _ _ _ => by simp)
  have hΨ : ∀ m w, Ψ m w = m ⬝ᵥ (fil w : Fin G.height → O) := fun _ _ => rfl
  have hΨker : LinearMap.ker Ψ = D'.Fil := by
    ext m
    rw [LinearMap.mem_ker, perp]
    constructor
    · intro hm f hf
      obtain ⟨w, hw⟩ := fil.surjective ⟨f, hf⟩
      have h5 := LinearMap.congr_fun hm w
      rwa [hΨ, hw] at h5
    · intro hm
      exact LinearMap.ext fun w => hm _ (fil w).2
  haveI : Module.Projective O ((Fin G.height → O) ⧸ D.Fil) := Module.Projective.of_equiv lie.symm
  obtain ⟨s, hs⟩ := Module.projective_lifting_property D.Fil.mkQ LinearMap.id D.Fil.mkQ_surjective
  let r : (Fin G.height → O) →ₗ[O] D.Fil :=
    (LinearMap.id - s ∘ₗ D.Fil.mkQ).codRestrict D.Fil fun x => by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub]
      have h5 := LinearMap.congr_fun hs (D.Fil.mkQ x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h5 ⊢
      rw [h5, sub_self]
  have hr : ∀ f : D.Fil, r f = f := fun f => by
    apply Subtype.ext
    have h0 : D.Fil.mkQ (f : Fin G.height → O) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 f.2
    simp [r, h0]
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    let φ : (Fin G.height → O) →ₗ[O] O := y ∘ₗ fil.symm.toLinearMap ∘ₗ r
    refine ⟨fun i => φ (Pi.single i 1), LinearMap.ext fun w => ?_⟩
    rw [hΨ, dot_single]
    simp [φ, hr]
  let lie' : ((Fin G.height → O) ⧸ D'.Fil) ≃ₗ[O] G.dual.Lie :=
    Submodule.quotEquivOfEq _ _ hΨker.symm ≪≫ₗ Ψ.quotKerEquivOfSurjective hΨsurj
  have hlie' : ∀ m, lie' (D'.Fil.mkQ m) = Ψ m := fun _ => rfl
  refine ⟨D', e', fil', lie', fun χ => ?_, fun y ψ => ?_⟩
  · have hf : fil' (hodgeTate G.dual χ) = filE (dlog G χ) := by
      simp only [fil', LinearEquiv.trans_apply]
      congr 1
      rw [LinearEquiv.symm_apply_eq, DlogSpan.pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate]
    rw [hf]
    change _ = Φ (dlog G χ)
    funext i
    change _ = lie (D.Fil.mkQ (Pi.single i 1)) (dlog G χ)
    rw [← hB, LinearEquiv.symm_apply_apply]
    change Matrix.toLin' ((D.G)ᵀ.map θ) (toO e' χ) i =
      pairingO hε e (Matrix.toLin' (D.G.map θ) (Pi.single i 1)) χ
    simp [pairingO, toO, he', E, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, θ,
      Pi.single_apply, mul_comm]
  · obtain ⟨m, rfl⟩ := hΨsurj y
    obtain ⟨t, rfl⟩ := (tateCongr O G.bidual).surjective ψ
    have hl : lie'.symm (Ψ m) = D'.Fil.mkQ m := by
      rw [LinearEquiv.symm_apply_eq]
      exact (hlie' m).symm
    rw [hl]
    change pairingO hε e' (D'.bb m) (tateMap G G.dual.dual O G.bidual.hom t) =
      Ψ m (dlog G.dual (tateMap G G.dual.dual O G.bidual.hom t))
    rw [← hodgeTate_apply, hΨ, ← hA]
    have hp : ∀ i, epsPairing hε G.dual (e'.symm (Pi.single i 1))
        (tateMap G G.dual.dual O G.bidual.hom t) = e t i := fun i => by
      rw [epsPairing, DetInv.pairing_dual_bidual]
      exact hdualb t i
    simp only [pairingO, hp]
    change Matrix.toLin' ((D.F)ᵀ.map θ) m ⬝ᵥ toO e t = m ⬝ᵥ Matrix.toLin' (D.F.map θ) (toO e t)
    rw [toLin'_transpose_dot]

end GlobalTheory.DualDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingSmulRightConj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.ActRight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_bar (H : Host E) (s : 𝓞 E) : H.bar (H.bar s) = s := by
  apply Subtype.ext
  show ((H.bar (H.bar s) : 𝓞 E) : E) = (s : E)
  rw [H.bar_eq, H.bar_eq]
  simp

theorem weilEq_act_adj (H : Host E) (K : Type) [Field K] [NumberField K] (σ₁ : K →+* ℂ)
    (A : PAT H (Sp (𝓞 K))) (a : 𝓞 E) :
    WeilEq A.t.PP.L (A.t.act.act (H.bar a)) (𝟙 _) A.t.PP.L (𝟙 _) (A.t.act.act a)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  have hl : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have key := (GlobalTheory.PairingFibre.lamEq_weilEq_over_ring hl (𝓞 K) A.pol A.pol A.pol A.pol
    (A.t.act.act (H.bar a)) (𝟙 _) (𝟙 _) (A.t.act.act a) (A.t.act.hom _) inferInstance inferInstance
    (A.t.act.hom a) ℂ (σ₁.comp (algebraMap (𝓞 K) K))).1
  apply key
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  have h := A.t.adj (H.bar a)
  rwa [bar_bar] at h

theorem weilEq_act_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f g : A.t.G ⟶ B.t.G), IsMonHom f → IsMonHom g →
    ∀ r s : 𝓞 E,
    WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f (A.t.act.act s ≫ g) A.t.PP.L (A.t.act.act (r * H.bar s)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f g _ _ r s h n x y c hn hx hy
  haveI := A.t.act.hom s
  haveI := A.t.act.hom r
  have hy' : (y ≫ A.t.act.act s) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hx' : (x ≫ A.t.act.act r) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have h1 := h n x (y ≫ A.t.act.act s) c hn hx hy'
  have h2 := weilEq_act_adj H K σ₁ A s n (x ≫ A.t.act.act r) y c hn hx' hy
  rw [← Category.assoc, h1, A.t.act.mul, ← Category.assoc, h2]
  simp only [Category.comp_id]

end GlobalTheory.CM.ActRight
end
end

