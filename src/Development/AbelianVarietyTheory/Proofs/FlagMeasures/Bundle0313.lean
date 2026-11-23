module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitive
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLattices
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGzLmap
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb.StabAct

open GlobalTheory.RowsOrb GlobalTheory.RowsOrb.Uniq

variable {D : D7} (X : HidaSetting D)

abbrev Xs : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range X.eX)

theorem P_X {x : (VS D).V} (hx : x ∈ Xs X) : P (VS D).hT X.eX X.fY x = 0 := by
  have hdY := dual_symm hh X.ef
  rw [P_apply, ← coord hdY hx, sub_self]

theorem P_Wb {w : (VS D).V} (hw : w ∈ Wb X) : P (VS D).hT X.eX X.fY w = w := by
  rw [P_apply]; simp [((mem_Wb X w).1 hw _).2]

theorem sub_proj_mem₂ (v : (VS D).V) : v - P (VS D).hT X.eX X.fY v ∈ Xs X := by
  rw [P_apply, sub_sub_cancel]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

variable {X}

theorem orth_e (δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hδ : ∀ x y, (VS D).hT (δ x) (δ y) = (VS D).hT x y)
    (hX : ∀ x ∈ Xs X, δ.symm x ∈ Xs X) {w : (VS D).V} (hw : w ∈ Wb X) (a : Fin D.R.rS) :
    (VS D).hT (X.eX a) (δ w) = 0 := by
  rw [← δ.apply_symm_apply (X.eX a), hδ]
  exact GlobalTheory.RowsOrb.Basic.hT_span_left X.eX w (fun b => ((mem_Wb X w).1 hw b).1)
    (hX _ (Submodule.subset_span ⟨a, rfl⟩))

variable (X)

def gl (δ : (VS D).V →ₗ[D.host.E] (VS D).V) (hS : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (δ w) = 0) :
    Wb X →ₗ[D.host.E] Wb X :=
  LinearMap.codRestrict (Wb X) (P (VS D).hT X.eX X.fY ∘ₗ δ ∘ₗ (Wb X).subtype)
    (fun w a => P_mem X.ee (dual_symm hh X.ef) (hS _ w.2) a)

theorem gl_inv (δ ε : (VS D).V →ₗ[D.host.E] (VS D).V) (hεδ : ∀ v, ε (δ v) = v)
    (hε : ∀ x ∈ Xs X, ε x ∈ Xs X) {w : (VS D).V} (hw : w ∈ Wb X) :
    P (VS D).hT X.eX X.fY (ε (P (VS D).hT X.eX X.fY (δ w))) = w := by
  have e : P (VS D).hT X.eX X.fY (δ w) = δ w - (δ w - P (VS D).hT X.eX X.fY (δ w)) := by abel
  rw [e, map_sub, hεδ, map_sub, P_X X (hε _ (sub_proj_mem₂ X _)), sub_zero, P_Wb X hw]

def ge (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h1 : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (γ w) = 0)
    (h2 : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (γ.symm w) = 0)
    (hX : ∀ x ∈ Xs X, γ x ∈ Xs X) (hX' : ∀ x ∈ Xs X, γ.symm x ∈ Xs X) : Wb X ≃ₗ[D.host.E] Wb X :=
  LinearEquiv.ofLinear (gl X (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h1)
    (gl X ((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) h2)
    (LinearMap.ext fun w => Subtype.ext (gl_inv X _ _ (fun v => γ.apply_symm_apply v) hX w.2))
    (LinearMap.ext fun w => Subtype.ext (gl_inv X _ _ (fun v => γ.symm_apply_apply v) hX' w.2))

theorem transport (u : D.what₂.Word) (δ : (VS D).V →ₗ[D.host.E] (VS D).V) (hX : ∀ x ∈ Xs X, δ x ∈ Xs X)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {v : (VS D).V}
    (hv : v ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X) :
    P (VS D).hT X.eX X.fY (δ v) ∈
      Λ.map (δ.restrictScalars (𝓞 D.host.E)) ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := by
  obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 hv
  rw [GlobalTheory.RowsOrb.Basic.mem_XO] at hx
  refine Submodule.mem_sup.2 ⟨δ l, Submodule.mem_map_of_mem hl,
    δ x - (δ (l + x) - P (VS D).hT X.eX X.fY (δ (l + x))), ?_, ?_⟩
  · rw [GlobalTheory.RowsOrb.Basic.mem_XO]
    exact Submodule.sub_mem _ (hX x hx) (sub_proj_mem₂ X _)
  · rw [map_add (f := _)]; abel

end GlobalTheory.RowsOrb.StabAct


open GlobalTheory.RowsOrb.StabAct GlobalTheory.RowsOrb.Uniq in
theorem GlobalTheory.RowsOrb.exists_gz_lmap : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∀ γ ∈ stabF D (X.Fu u),
    ∃ g : GlobalTheory.RowsOrb.Gz X u, ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V,
      g • GlobalTheory.RowsOrb.Lmap X u Λ = GlobalTheory.RowsOrb.Lmap X u (Formalism.HermitianLatticesTheory.gmap γ Λ) := by
  intro D X u γ hγ
  obtain ⟨hiso, hXa, hz⟩ := hγ
  have hδ : ∀ x y, (VS D).hT (γ x) (γ y) = (VS D).hT x y := hiso
  have hδ' : ∀ x y, (VS D).hT (γ.symm x) (γ.symm y) = (VS D).hT x y := fun x y => by
    rw [← hδ, γ.apply_symm_apply, γ.apply_symm_apply]
  have hXr : (X.Fu u).Xa D.R.rS = Xs X := by
    simp only [FlagG.Xa, HidaSetting.Fu_e]
    congr 1
    ext v
    simp
  have hmap := hXa D.R.rS
  rw [hXr] at hmap
  have hX : ∀ x ∈ Xs X, γ x ∈ Xs X := fun x hx => by
    rw [← hmap]; exact Submodule.mem_map_of_mem hx
  have hX' : ∀ x ∈ Xs X, γ.symm x ∈ Xs X := fun x hx => by
    rw [← hmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have h1 := fun w (hw : w ∈ GlobalTheory.RowsOrb.Wb X) a => orth_e γ hδ hX' hw a
  have h2 := fun w (hw : w ∈ GlobalTheory.RowsOrb.Wb X) a => orth_e γ.symm hδ' (fun x hx => by simpa using hX x hx) hw a
  have hz' : γ (X.zu u) = X.zu u := by rw [← HidaSetting.flagZVector]; exact hz
  let e := ge X γ h1 h2 hX hX'
  have he : ∀ w, ((e w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = P (VS D).hT X.eX X.fY (γ w) := fun w => rfl
  have he' : ∀ w, ((e.symm w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = P (VS D).hT X.eX X.fY (γ.symm w) := fun w => rfl
  have hi : e ∈ Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hb X) := by
    intro x y
    rw [GlobalTheory.RowsOrb.hb_apply, GlobalTheory.RowsOrb.hb_apply, he, he, P_apply, P_apply,
      P_iso hh X.ee (orth_e γ hδ hX' x.2) (orth_e γ hδ hX' y.2), hδ]
  have hs : (⟨e, hi⟩ : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hb X)) ∈ GlobalTheory.RowsOrb.Gz X u := by
    rw [MulAction.mem_stabilizer_iff]
    show e (GlobalTheory.RowsOrb.zb X u) = GlobalTheory.RowsOrb.zb X u
    apply Subtype.ext
    rw [he, GlobalTheory.RowsOrb.zb_coe, hz']
    exact P_Wb X (GlobalTheory.RowsOrb.zb X u).2
  refine ⟨⟨⟨e, hi⟩, hs⟩, fun Λ => ?_⟩
  have hback : (Formalism.HermitianLatticesTheory.gmap γ Λ).map
      (((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars
        (𝓞 D.host.E)) = Λ := by
    ext v
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hv
      exact ⟨γ v, ⟨v, hv, rfl⟩, by simp⟩
  show Formalism.HermitianLatticesTheory.gmap e (GlobalTheory.RowsOrb.Lmap X u Λ) = _
  ext w'
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h := transport X u (γ : (VS D).V →ₗ[D.host.E] (VS D).V) hX Λ ((GlobalTheory.RowsOrb.mem_Lmap X u Λ w).1 hw)
    exact (GlobalTheory.RowsOrb.mem_Lmap X u _ _).2 h
  · intro hw'
    refine ⟨e.symm w', ?_, e.apply_symm_apply w'⟩
    have h := transport X u ((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) hX'
      (Formalism.HermitianLatticesTheory.gmap γ Λ) ((GlobalTheory.RowsOrb.mem_Lmap X u _ w').1 hw')
    rw [hback] at h
    exact (GlobalTheory.RowsOrb.mem_Lmap X u _ _).2 h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameComplementRealPlaces
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.CFrame

theorem hJ_rv_gen (I : AutInst) (v : InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  have hPi : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hJv : I.J.map (I.φ v) = ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ := by
    rw [← I.P_spec v]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hPi, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hPi, Matrix.conjTranspose_one, Matrix.one_mul]
  unfold hJ rv
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hJv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, Pi.star_apply, Matrix.map_apply, Formalism.UG.hform, map_sum, map_mul,
    starRingEnd_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [I.cm.cmUnram.2.1]
  simp only [RCLike.star_def]
  ring

theorem hform_cols {A : Type} [CommRing A] {n ι : Type} [Fintype n] [Fintype ι] (σ : A →+* A)
    (J : Matrix n n A) (Q : Matrix n ι A) (α β : ι) :
    Formalism.UG.hform σ J (fun i => Q i α) (fun i => Q i β) = ((Q.map σ)ᵀ * J * Q) α β := by
  simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

variable {D : D7} (X : HidaSetting D)

theorem hJ_crd' (v : InfinitePlace X.B.I.F) (a b : (VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd a)) (rv X.B.I v (X.crd b)) = X.B.I.φ v (X.ιE.symm ((VS D).hT a b)) := by
  rw [hJ_rv_gen, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X a b, RingEquiv.symm_apply_apply]

theorem card_eq : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  rw [X.n_eq]
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

end GlobalTheory.St.CFrame

namespace GlobalTheory.St.CFrame

variable {D : D7} (X : HidaSetting D)

theorem gram_blocks (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hw : WittX X u wt) :
    (∀ v a b, hJ (X.B.I.ε v) (rvV X v (qFr wt a)) (rvV X v (qFr wt b)) =
        X.B.I.φ v (X.ιE.symm (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) a b))) ∧
    (∀ v c a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (rvV X v (qFr wt a)) = 0 ∧
        hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (rvV X v (qFr wt a)) = 0) ∧
    (∀ v a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rvV X v (qFr wt a)) = 0) ∧
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hq, he, hf, hz, _, hblk⟩ := _root_.GlobalTheory.St.qFrame_basis_gram D X u wt hw
  have hent : ∀ α β, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (fun i => Q i α) (fun i => Q i β) =
      Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 G' α β := by
    intro α β
    rw [hform_cols, hblk]
  have colq : ∀ j, (fun i => Q i (Sum.inl j)) = X.crd (qFr wt j) := fun j => funext fun i => hq j i
  have cole : ∀ a, (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := fun a => funext fun i => he a i
  have colf : ∀ a, (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a := fun a => funext fun i => hf a i
  have colz : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext fun i => hz i
  refine ⟨fun v a b => ?_, fun v c a => ⟨?_, ?_⟩, fun v a => ?_, ?_⟩
  · have h := hent (Sum.inl a) (Sum.inl b)
    rw [colq, colq] at h
    rw [rvV, rvV, hJ_rv_gen, h]
    rfl
  · have h := hent (Sum.inr (Sum.inl c)) (Sum.inl a)
    rw [cole, colq] at h
    rw [rvV, hJ_rv_gen, h]
    simp
  · have h := hent (Sum.inr (Sum.inr (Sum.inl c))) (Sum.inl a)
    rw [colf, colq] at h
    rw [rvV, hJ_rv_gen, h]
    simp
  · have h := hent (Sum.inr (Sum.inr (Sum.inr ()))) (Sum.inl a)
    rw [colz, colq] at h
    rw [rvV, hJ_rv_gen, h]
    simp
  · intro h0
    have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.2 X.B.I.J_det
    have e1 : (Q.map (starRingEnd X.B.I.E))ᵀ * (Qi.map (starRingEnd X.B.I.E))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    have hinv : ((Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q) *
        (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J X.B.I.J⁻¹,
        Matrix.mul_nonsing_inv _ hJu, Matrix.one_mul, e1]
    rw [hblk] at hinv
    have hd := congrArg Matrix.det hinv
    rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one] at hd
    have hA : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det = 0 := by
      rw [show ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det =
          X.ιE.symm.toRingHom (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det from
          (RingHom.map_det X.ιE.symm.toRingHom _).symm, h0, map_zero]
    rw [hA, zero_mul, zero_mul] at hd
    exact zero_ne_one hd

end GlobalTheory.St.CFrame

namespace GlobalTheory.St.CFrame

theorem frame_of_type : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ o : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), (∀ τ, (o.1 τ)ᴴ * Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D) τ * o.1 τ = 1) ∧ ∀ s ∈ Hinf X u, ∃ m : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ, ∀ τ, m τ ∈ Matrix.unitaryGroup (Fin (D.R.N 0)) ℂ ∧ (m τ).submatrix (Fin.cast D.R.N_zero.symm) (Fin.cast D.R.N_zero.symm) = matW X.B.I (X.wfr u (X.pl.symm τ)) (X.pl.symm τ) s ∧ sTil X wt s τ = o.1 τ * m τ * (o.1 τ)⁻¹ := by
  intro D X u wt hw
  obtain ⟨hqq, hqef, hqz, hdet⟩ := gram_blocks X u wt hw
  have hgQ : ∀ v, gramQ X wt v = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map (Formalism.L2.Forms.embT D (X.pl v)) := by
    intro v
    ext a b
    simp only [gramQ, Matrix.of_apply, Matrix.map_apply]
    rw [hqq, X.φ_eq, RingEquiv.apply_symm_apply]
    rfl
  have hGu : ∀ v, IsUnit (gramQ X wt v).det := by
    intro v
    rw [hgQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hdet)
  have hJm : ∀ v, IsUnit (Formalism.REAL.Jm (X.B.I.ε v)).det :=
    fun v => Matrix.isUnit_det_of_left_inverse (Formalism.REAL.Jm_mul_self _)
  have key := fun v => GlobalTheory.frame_complement_change_of_basis X.B.I.n D.R.rS D.R.k (D.R.N 0) D.R.N_zero.symm (Formalism.REAL.Jm (X.B.I.ε v))
    (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (X.wfr u v)
    (fun a => rvV X v (qFr wt a)) (card_eq X) (Formalism.REAL.Jm_conjTranspose _) (hJm v)
    (fun a b => by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.eX a) (X.eX b)).trans ?_
      rw [X.ee]; simp)
    (fun a b => by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.fY a) (X.fY b)).trans ?_
      rw [X.ff]; simp)
    (fun a b => by
      show hJ (X.B.I.ε v) _ _ = _
      refine (hJ_crd' X v (X.eX a) (X.fY b)).trans ?_
      rw [X.ef]; split_ifs <;> simp)
    (fun a => ⟨by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.eX a) (X.zu u)).trans ?_
      rw [(X.zu_orth u a).1]; simp, by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.fY a) (X.zu u)).trans ?_
      rw [(X.zu_orth u a).2]; simp⟩)
    (by
      show hJ (X.B.I.ε v) _ _ ≠ 0
      refine (hJ_crd' X v (X.zu u) (X.zu u)).trans_ne ?_
      rw [X.zu_norm]
      have hT : (((D.mem u).A.T : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
      simpa using hT)
    (X.wfr_on u v) (X.wfr_perp u v)
    (fun a => ⟨fun c => ⟨(hqef v c a).1, (hqef v c a).2⟩, hqz v a⟩)
    (gramQ X wt v) (fun a b => rfl) (hGu v)
  choose oo hoo using key
  refine ⟨⟨fun τ => oo (X.pl.symm τ), fun τ => (hoo _).1⟩, fun τ => ?_, fun s hs => ?_⟩
  · have h := (hoo (X.pl.symm τ)).2.1
    rw [hgQ, Equiv.apply_symm_apply] at h
    exact h
  · have hfix : ∀ v, ∀ x ∈ fixSet X u, uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v x := hs
    have hm := fun τ => (hoo (X.pl.symm τ)).2.2 (uMat (s (X.pl.symm τ))) (s (X.pl.symm τ)).2
      (fun a => ⟨hfix _ _ (Or.inl (Or.inl ⟨a, rfl⟩)), hfix _ _ (Or.inl (Or.inr ⟨a, rfl⟩))⟩)
      (hfix _ _ (Or.inr rfl))
    choose m hmU hmW hmT using hm
    exact ⟨m, fun τ => ⟨hmU τ, hmW τ, hmT τ⟩⟩

end GlobalTheory.St.CFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrder
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CompletedSelfDual

open GlobalTheory.AdelicU GlobalTheory.AdelicU.SelfDual GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces

theorem mem_maxOrder_iff_mem_intLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    z ∈ maxOrder F E v ↔ z ∈ intLoc F E v := by
  constructor
  · intro hz
    rw [mem_intLoc_iff_absFin_le_one, absFin_le_iff]
    intro τ
    obtain ⟨p, hp, hpz⟩ := (mem_maxOrder F E v z).1 hz
    let f : v.adicCompletionIntegers F →+* (valBar F v).integer :=
      ((algebraMap (Fv F v) (FvBar F v)).comp (v.adicCompletionIntegers F).subtype).codRestrict _ fun a => by
        change absBar F v (algebraMap (Fv F v) (FvBar F v) a) ≤ 1
        rw [absBar_algebraMap]
        exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 a.2
    refine (Valuation.integer.integers (valBar F v)).mem_of_integral (x := finEmb F v τ z)
      ⟨p.map f, hp.map _, ?_⟩
    have := congrArg (finEmb F v τ : Fv F v ⊗[F] E →+* FvBar F v) hpz
    rw [Polynomial.hom_eval₂, map_zero] at this
    rw [Polynomial.eval₂_map, ← this]
    congr 1
    ext a
    exact ((finEmb F v τ).commutes (a : Fv F v)).symm
  · refine intLoc_induction (p := fun z => z ∈ maxOrder F E v) (fun a ha x => ?_) (zero_mem _)
      (fun _ _ => add_mem) (fun _ => neg_mem)
    have h1 : (1 : Fv F v) ⊗ₜ[F] (x : E) ∈ maxOrder F E v := by
      letI := (intToEv F E v).toAlgebra
      exact (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (algebraMap ℤ _) (inclR (F := F) (E := E) (Fv F v))
        (RingHom.ext_int _ _)
    have h2 : a ⊗ₜ[F] (1 : E) ∈ maxOrder F E v :=
      RingHom.isIntegralElem_map (intToEv F E v) (x := ⟨a, ha⟩)
    simpa using mul_mem h2 h1

theorem exists_isSelfDualLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), IsHermND σ J → Submodule.IsLattice E L → (∀ y : Fin n → E, y ∈ L ↔ ∀ x ∈ L, hE σ J x y ∈ (algebraMap (𝓞 E) E).range) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ Lv : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin n → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v Lv ∧ ∀ y, y ∈ Lv ↔ y ∈ GlobalTheory.AdelicU.latLoc F L v := by
  intro F E _ _ _ _ _ σ n J L hJ hL hsd v
  classical
  let Lv : Submodule (maxOrder F E v) (Fin n → Fv F v ⊗[F] E) :=
    { carrier := latLoc F L v
      zero_mem' := zero_mem _
      add_mem' := fun h h' => add_mem h h'
      smul_mem' := fun c _ hy =>
        (latLoc F L v).smul_mem ⟨c.1, (mem_maxOrder_iff_mem_intLoc v _).1 c.2⟩ hy }
  have hmem : ∀ y, y ∈ Lv ↔ y ∈ latLoc F L v := fun _ => Iff.rfl
  have hfull : Submodule.IsFullLattice E L := by
    refine { toIsLattice := hL, span_eq_top := eq_top_iff.mpr fun y _ => ?_ }
    obtain ⟨s, hs⟩ := hL.fg
    obtain ⟨d, hd, hden⟩ := exists_integral_multiples ℤ ℚ
      (s.image fun x => hE σ J x y)
    have hdE : (d : E) ≠ 0 := by exact_mod_cast hd
    have hy : (d : E) • y ∈ L := by
      apply (hsd _).2
      intro x hx
      rw [← hs] at hx
      have hint : IsIntegral ℤ (hE σ J x ((d : E) • y)) := by
        induction hx using Submodule.span_induction with
        | mem x hx =>
          have hh := hden (hE σ J x y) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
          convert hh using 1 <;> simp [hE, Formalism.UG.hform, Pi.smul_apply,
            smul_eq_mul, Finset.mul_sum, Finset.sum_mul, zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
        | zero => simpa [hE, Formalism.UG.hform] using (isIntegral_zero : IsIntegral ℤ (0 : E))
        | add x z _ _ hx hz =>
          convert hx.add hz using 1 <;>
            simp [hE, Formalism.UG.hform, add_mul, Finset.sum_add_distrib]
        | smul a x _ hx =>
          have ha : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toRingHom.toIntAlgHom
          convert ha.mul hx using 1 <;>
            simp [hE, Formalism.UG.hform, Pi.smul_apply, ← algebraMap_smul E, smul_eq_mul, map_mul,
              Finset.mul_sum, mul_assoc]
      exact ⟨⟨_, hint⟩, rfl⟩
    have hyspan : (d : E) • y ∈ Submodule.span E (L : Set (Fin n → E)) := Submodule.subset_span hy
    have := Submodule.smul_mem (Submodule.span E (L : Set (Fin n → E))) (d : E)⁻¹ hyspan
    simpa [← smul_smul, hdE] using this
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := exists_frame L hfull
  have h2 := map_mul_eq_one (F := F) (Fv F v) h1
  have hcol : ∀ j, (fun i => S.map (inclR (F := F) (Fv F v)) i j) ∈ Lv := fun j =>
    tmul_mem_latLoc (one_mem _) (hS j)
  refine ⟨Lv, ⟨?_, ?_, fun y => ?_⟩, hmem⟩
  · refine ⟨Finset.univ.image fun j i => S.map (inclR (F := F) (Fv F v)) i j, le_antisymm ?_ fun y hy => ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      exact hcol j
    · rw [eq_sum_col h2 y]
      refine sum_mem fun j _ => ?_
      exact Submodule.smul_mem _ (⟨_, (mem_maxOrder_iff_mem_intLoc v _).2
        ((mem_latLoc_iff_of_frame h1 hS hΦ v y).1 hy j)⟩ : maxOrder F E v)
        (Submodule.subset_span (Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩))
  · refine eq_top_iff.2 fun y _ => ?_
    rw [eq_sum_col h2 y]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hcol j))
  · have h3 : latLoc F L v = dualLoc σ J L v := (forall_isSelfDualAt_iff hJ.2 hfull).2 hsd v
    simp only [mem_maxOrder_iff_mem_intLoc]
    rw [hmem, h3]
    exact Iff.rfl

end GlobalTheory.CompletedSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndicatorCompletedLatticeEqFinprodLocal
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicU

theorem eventually_vecLoc_mem_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) (y : Fin n → Af F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, vecLoc v y ∈ latLoc F L v := by
  letI := hL
  haveI := isLattice_stdLattice (E := E) (n := n)
  filter_upwards [eventually_latLoc_eq F L (stdLattice E n),
    Filter.eventually_all.2 fun i => eventually_map_evalV_mem_intLoc (y i)] with v h h1
  rw [h, mem_latLoc_stdLattice]
  exact h1

theorem indicator_latHat_eq_finprod :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
      (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ X : Fin 1 → Fin n → Af F ⊗[F] E,
      {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}.indicator
        (1 : (Fin 1 → Fin n → Af F ⊗[F] E) → ℂ) X =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator
          (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) := by
  intro F E _ _ _ _ _ n L hL X
  have key : ∀ v : HeightOneSpectrum (𝓞 F), vecLoc v (X 0) ∈ latLoc F L v →
      {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator
          (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) = 1 := fun v hv =>
    Set.indicator_of_mem (s := {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}) hv _
  by_cases h : X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))
  · rw [Set.indicator_of_mem
      (s := {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}) h,
      finprod_congr fun v => key v ((mem_latHat_iff hL.fg _).1 h v), finprod_one]
    rfl
  · rw [Set.indicator_of_notMem
      (s := {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}) h]
    rw [mem_latHat_iff hL.fg, not_forall] at h
    obtain ⟨v, hv⟩ := h
    refine (finprod_eq_zero _ v ?_ ?_).symm
    · exact Set.indicator_of_notMem
        (s := {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}) hv _
    · exact Set.Finite.subset (Filter.eventually_cofinite.1 (eventually_vecLoc_mem_latLoc L hL (X 0)))
        fun u hu hu' => hu (key u hu')

end GlobalTheory.AdelicU
end

