module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsWt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedNonzero
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section

namespace GlobalTheory.UnipClosed

theorem isClosed_unip (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁) (hx : H'.x ≠ 0) :
    IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  set x : Fin d → AE F E := incV F H'.x with hxdef
  set ι : Matrix (Fin d) (Fin d₁) (AE F E) := incM F H'.ι

  set S : Set (UA σ W.J) := {u | mat u *ᵥ x = x ∧ ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} with hS
  obtain ⟨k, hk⟩ : ∃ k, H'.x k ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  have hcu : IsUnit (x k) := by
    have : x k = inclR (F := F) (AF F) (H'.x k) := rfl
    rw [this]; exact (IsUnit.mk0 _ hk).map _
  set c : (AE F E)ˣ := hcu.unit
  have hc : (c : AE F E) = x k := hcu.unit_spec
  have hline : ∀ v w : Fin d → AE F E, (∃ a : AE F E, w = v + a • x) ↔ w = v + ((w - v) k * ↑c⁻¹) • x := by
    intro v w
    constructor
    · rintro ⟨a, rfl⟩
      congr 2
      simp only [add_sub_cancel_left, Pi.smul_apply, smul_eq_mul]
      rw [← hc, mul_assoc, Units.mul_inv, mul_one]
    · intro h; exact ⟨_, h⟩
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hSc : IsClosed S := by
    have h1 : IsClosed {u : UA σ W.J | mat u *ᵥ x = x} :=
      isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
    have h2 : IsClosed {u : UA σ W.J | ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun z => ?_
      simp_rw [hline]
      have hf : Continuous fun u : UA σ W.J => mat u *ᵥ (ι *ᵥ z) := hm.matrix_mulVec continuous_const
      have hg : Continuous fun u : UA σ W.J => ((mat u *ᵥ (ι *ᵥ z) - ι *ᵥ z) k * ↑c⁻¹) :=
        ((continuous_apply k).comp (hf.sub continuous_const)).mul continuous_const
      exact isClosed_eq hf (continuous_const.add (hg.smul (continuous_const : Continuous fun _ : UA σ W.J => x)))
    exact h1.inter h2
  have hsub : ∃ H : Subgroup (UA σ W.J), (H : Set (UA σ W.J)) = S := by
    refine ⟨{ carrier := S, one_mem' := ?_, mul_mem' := ?_, inv_mem' := ?_ }, rfl⟩
    · rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
      refine ⟨by rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
      obtain ⟨a, ha⟩ := hv2 z
      obtain ⟨b, hb⟩ := hu2 z
      refine ⟨b + a, ?_⟩
      rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hu1, add_smul, add_assoc]
    · exact ⟨by simp [GlobalTheory.StabHaar.mat_one], fun z => ⟨0, by simp [GlobalTheory.StabHaar.mat_one]⟩⟩
    · rintro u ⟨hu1, hu2⟩
      have e1 : mat u⁻¹ *ᵥ x = x := by
        conv_lhs => rw [← hu1]
        rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
      refine ⟨e1, fun z => ?_⟩
      obtain ⟨a, ha⟩ := hu2 z
      refine ⟨-a, ?_⟩
      have : mat u⁻¹ *ᵥ (mat u *ᵥ (ι *ᵥ z)) = ι *ᵥ z := by
        rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
      rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, e1] at this
      rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, this]
  obtain ⟨H, hH⟩ := hsub
  have : unip σ W H' = H := by
    apply le_antisymm
    · rw [unip, Subgroup.closure_le]; exact hH.symm ▸ subset_rfl
    · intro g hg
      have : g ∈ S := hH ▸ hg
      exact Subgroup.subset_closure this
  rw [this, hH]; exact hSc

end GlobalTheory.UnipClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalFinitenessRegularSemisimpleCentraliz
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.LocFinU

theorem bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∃ Ω : Set (UL n w), IsCompact Ω ∧ (cptPart (twCent (MonoidHom.id (UL n w)) y) : Set (UL n w)) ⊆ Ω := by
  intro E _ _ _ hE n w y hy
  obtain ⟨Ω, hΩ, hsub⟩ := _root_.GlobalTheory.CentCpt.main E hE n w y hy
  refine ⟨Ω, hΩ, fun t ht => ?_⟩
  have hc : ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
    intro a ha b hb
    have ha' : a.1.val * y.1.val =
        y.1.val * a.1.val :=
      by
        have h0 : a * y = y * a := ha
        have := congrArg (fun g : UL n w => g.1.val) h0
        simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have hb' : b.1.val * y.1.val =
        y.1.val * b.1.val :=
      by
        have h0 : b * y = y * b := hb
        have := congrArg (fun g : UL n w => g.1.val) h0
        simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have := _root_.GlobalTheory.commute_of_commute_separable_charpoly _ n _ _ _ hy ha' hb'
    exact Subtype.ext (Units.ext this)
  have := cptPart_subset_of_comm _ hc ht
  exact hsub t this.1 this.2

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

theorem conj_map_eq {G : Type} [Group G] (x : G) (K : Subgroup G) :
    (K.map (MulAut.conj x).toMonoidHom : Set G) = (fun k => x * k * x⁻¹) '' (K : Set G) := by
  ext g
  simp [Subgroup.coe_map, MulAut.conj_apply]

theorem locFin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → (∀ x : UL n w, twCent (MonoidHom.id _) y ⊓ (KL n w).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id _) y) ∧ (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id _) y)) ≠ 0) ∧ ∀ C : Set (UL n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) y : Set (UL n w)) (K' : Set (UL n w)) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite := by
  intro E _ _ _ hE n w y hy K' hK'
  obtain ⟨hK'o, -, -⟩ := hK'
  obtain ⟨Ω, hΩ, hsub⟩ := bound E hE n w y hy
  refine ⟨fun x => ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨htT, htK⟩ := Subgroup.mem_inf.1 ht
    apply Subgroup.subset_closure
    refine ⟨htT, ?_⟩
    have hc : IsCompact ((KL n w).map (MulAut.conj x).toMonoidHom : Set (UL n w)) := by
      rw [conj_map_eq]
      exact (isCompact_KL n w).image ((continuous_const.mul continuous_id).mul continuous_const)
    refine hc.of_isClosed_subset isClosed_closure ?_
    exact closure_minimal (Subgroup.zpowers_le.2 htK) hc.isClosed
  · have hP : cptPart (twCent (MonoidHom.id _) y) ≤ twCent (MonoidHom.id _) y :=
      (Subgroup.closure_le _).2 (fun t ht => ht.1)
    have hU : IsOpen ((K'.map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (UL n w)) := by
      rw [conj_map_eq]
      exact ((Homeomorph.mulLeft x).trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hK'o
    have h := relIndex_ne_zero_of_subset_cpt _ _ hU Ω hΩ hsub
    have e : (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf
        (cptPart (twCent (MonoidHom.id _) y)) =
        (K'.map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart (twCent (MonoidHom.id _) y)) := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hP z.2, h⟩⟩
    unfold Subgroup.relIndex at h ⊢
    rwa [e]
  · intro C hC
    obtain ⟨Ω', hΩ', horb⟩ := _root_.GlobalTheory.OrbitU.orbit_cpt_U E hE n w y hy C hC
    obtain ⟨s, hs⟩ := hΩ'.elim_finite_subcover (fun g : Ω' => (g : UL n w) • (K' : Set (UL n w)))
      (fun g => hK'o.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, K'.one_mem, mul_one x⟩⟩)
    refine (s.finite_toSet.image
      (fun g : Ω' => DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) y) K' (g : UL n w))).subset ?_
    intro q hq
    obtain ⟨t, ht, ω, hω, heq⟩ := horb _ hq
    have := hs hω
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, k, hk, hik⟩ := this
    refine ⟨i, hi, ?_⟩
    conv_rhs => rw [← Quotient.out_eq q]
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨t, ht, k, hk, ?_⟩
    rw [heq, ← hik]
    simp only [smul_eq_mul, mul_assoc]

end GlobalTheory.LocFinU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairOfTransposedGramInverseGram
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger

theorem matchPair_cA_eq_sigR (D : D7) (x : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig x = sigR (AF D.host.F) D.sp.cm.sig x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, sigR]
  | add x y hx hy => simp_all

theorem matchPair_inv_transpose {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (Bm Bi P Q Cm Ci : Matrix n n R) (hBB : Bm * Bi = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hCC : Ci * Cm = 1) (hb : Bmᵀ * P * Cm = P) : Ci * Q * Biᵀ = Q := by
  have e1 : Biᵀ * Bmᵀ = 1 := by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  have e2 : P * Cm = Biᵀ * P := by
    calc P * Cm = (Biᵀ * Bmᵀ) * P * Cm := by rw [e1, Matrix.one_mul]
      _ = Biᵀ * (Bmᵀ * P * Cm) := by simp only [Matrix.mul_assoc]
      _ = Biᵀ * P := by rw [hb]
  have e3 : Cm * Q = Q * Biᵀ := by
    calc Cm * Q = (Q * P) * Cm * Q := by rw [hQP, Matrix.one_mul]
      _ = Q * (P * Cm) * Q := by simp only [Matrix.mul_assoc]
      _ = Q * Biᵀ * (P * Q) := by rw [e2]; simp only [Matrix.mul_assoc]
      _ = Q * Biᵀ := by rw [hPQ, Matrix.mul_one]
  calc Ci * Q * Biᵀ = Ci * (Q * Biᵀ) := Matrix.mul_assoc _ _ _
    _ = Ci * (Cm * Q) := by rw [e3]
    _ = Q := by rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]

theorem matchPair_map_cA (D : D7) {n m : ℕ} (M : Matrix (Fin n) (Fin m) (AE D)) :
    M.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = M.map (sigR (AF D.host.F) D.sp.cm.sig) := by
  ext i j; exact matchPair_cA_eq_sigR D (M i j)

theorem matchPair_memT (D : D7) (T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (hA : JA = T.gramᵀ)
    (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)) : (a.1 : GL (Fin T.rank) (AE D)) ∈ HR (AF D.host.F) D.sp.cm.sig T.gram := by
  have ha : a.1.1ᵀ * incM D.host.F JA * a.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JA := a.2
  show Formalism.UG.cT _ _ * _ * _ = _
  have := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA] at this
  unfold Formalism.UG.cT JR
  rw [← matchPair_map_cA]
  have e : (incM D.host.F T.gramᵀ)ᵀ = incM D.host.F T.gram := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_map]
  rw [e] at this
  exact (Matrix.mul_assoc _ _ _).trans this

theorem matchPair_keeps_inv_gram (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) :
    b.1.1ᵀ * incM D.host.F S.gram⁻¹ * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F S.gram⁻¹ := by
  have hb : b.1.1ᵀ * incM D.host.F JB * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JB := b.2
  have hxi : IsUnit (incA D D.host.xi0) := (isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have hsc : (incM D.host.F (D.host.xi0 • S.gram⁻¹) : Matrix (Fin S.rank) (Fin S.rank) (AE D)) =
      (incA D D.host.xi0 : AE D) • (incM D.host.F S.gram⁻¹ : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, incA]
  have t1 : ∀ (r : AE D) (X Y : Matrix (Fin S.rank) (Fin S.rank) (AE D)), X * (r • Y) = r • (X * Y) :=
    fun r X Y => Matrix.mul_smul X r Y
  have t2 : ∀ (r : AE D) (X Y : Matrix (Fin S.rank) (Fin S.rank) (AE D)), (r • X) * Y = r • (X * Y) :=
    fun r X Y => Matrix.smul_mul r X Y
  have e1 := congrArg (fun M => ξ • M) hb
  rw [← t2, ← t1, hB, hsc] at e1
  have e2 : b.1.1ᵀ * ((incA D D.host.xi0 : AE D) • incM D.host.F S.gram⁻¹) * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (incA D D.host.xi0 : AE D) • (b.1.1ᵀ * incM D.host.F S.gram⁻¹ * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) := by
    rw [t1, t2]
  rw [e2] at e1
  exact hxi.smul_left_cancel.1 e1


set_option maxHeartbeats 1000000 in
theorem matchPair_memS (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) :
    ∃ G : GL (Fin S.rank) (AE D), G.1 = (b⁻¹).1.1ᵀ ∧ G ∈ HR (AF D.host.F) D.sp.cm.sig S.gram := by
  have hBB : b.1.1 * (b⁻¹).1.1 = 1 := Units.mul_inv b.1
  have hBB' : (b⁻¹).1.1 * b.1.1 = 1 := Units.inv_mul b.1
  have hdet : IsUnit S.gram.det := (Formalism.L2.Theta.gram_det_ne S).isUnit
  have hPQ : incM D.host.F S.gram⁻¹ * incM D.host.F S.gram = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP : incM D.host.F S.gram * incM D.host.F S.gram⁻¹ = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hCC : (b⁻¹).1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = 1 := by
    have := map_mul ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig).toRingHom.mapMatrix :
      Matrix (Fin S.rank) (Fin S.rank) (AE D) →+* Matrix (Fin S.rank) (Fin S.rank) (AE D)) (b⁻¹).1.1 b.1.1
    rw [hBB', map_one] at this
    exact this.symm
  have key := matchPair_inv_transpose _ _ _ _ _ _ hBB hPQ hQP hCC (matchPair_keeps_inv_gram D S JB ξ hB b)
  refine ⟨⟨(b⁻¹).1.1ᵀ, b.1.1ᵀ, by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩, rfl, ?_⟩
  show Formalism.UG.cT _ _ * _ * _ = _
  unfold Formalism.UG.cT JR
  rw [← matchPair_map_cA, Matrix.transpose_map, Matrix.transpose_transpose]
  exact key

theorem match_pair : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  intro D S T JA JB ξ hA hB a b
  obtain ⟨G, hG, hGm⟩ := matchPair_memS D S JB ξ hB b
  exact ⟨⟨G, hGm⟩, ⟨a.1, matchPair_memT D T JA hA a⟩, rfl, hG⟩

end GlobalTheory.WeilSchrodinger

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightUpperUnitriangularIdempotentIndepCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

open Matrix

namespace GlobalTheory.BadCount.WtPsi

open Formalism.L2.SG.Pf.AllRowsWt Formalism.L2.SG.Pf.AllRowsTr

variable {g : ℕ} [Fact g.Prime] {N : ℕ} (c : ZMod g)

theorem posN_lt {a : ℕ} (h : a < N) : posN 0 N a = a := by
  unfold posN; simp [h]

theorem sdg_conj (hc : c ≠ 0) (u : Matrix (Fin N) (Fin N) (ZMod g)) :
    ∑ i ∈ Finset.range (N - 1), entN (diagonal (fun i : Fin N => (tN 0 N c i)⁻¹) * u *
      diagonal (fun i : Fin N => tN 0 N c i)) i (i + 1) = c * ∑ i ∈ Finset.range (N - 1), entN u i (i + 1) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [entN_conj, pair 0 N c hc (by rw [posN_lt (by omega), posN_lt (by omega)])]

theorem uniUp_conj (hc : c ≠ 0) (u : Matrix (Fin N) (Fin N) (ZMod g)) :
    IsUniUp (diagonal (fun i : Fin N => (tN 0 N c i)⁻¹) * u * diagonal (fun i : Fin N => tN 0 N c i)) ↔ IsUniUp u := by
  have h := PJ_conj 0 N c hc u
  unfold PJ at h
  have hv : ∀ M : Matrix (Fin N) (Fin N) (ZMod g), ∀ a, N ≤ a → a < N → entN M a N = 0 :=
    fun _ a h1 h2 => absurd h2 (by omega)
  exact ⟨fun x => (h.1 ⟨x, hv _⟩).1, fun x => (h.2 ⟨x, hv _⟩).1⟩

theorem eU_conj (hc : c ≠ 0) (ψ : AddChar (ZMod g) ℂ) :
    haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
    MonoidAlgebra.single (T 0 N c hc) 1 * eU g N ψ * MonoidAlgebra.single (T 0 N c hc)⁻¹ 1 =
      eU g N (ψ.mulShift c) := by
  classical
  have : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  unfold eU eDat
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  simp only [MonoidAlgebra.single_mul_single, one_mul, mul_one]
  refine Finset.sum_nbij' (fun u => T 0 N c hc * u * (T 0 N c hc)⁻¹) (fun v => (T 0 N c hc)⁻¹ * v * T 0 N c hc)
    ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    show IsUniUp ((T 0 N c hc * u * (T 0 N c hc)⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g))
    rw [← uniUp_conj c hc, ← T_conj_val 0 N c hc]
    have e : (T 0 N c hc)⁻¹ * (T 0 N c hc * u * (T 0 N c hc)⁻¹) * T 0 N c hc = u := by group
    rw [e]; exact hu
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    show IsUniUp (((T 0 N c hc)⁻¹ * v * T 0 N c hc : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g))
    rw [T_conj_val, uniUp_conj c hc]; exact hv
  · intro u _; group
  · intro v _; group
  · intro u hu
    have e : (u : GL (Fin N) (ZMod g)) = (T 0 N c hc)⁻¹ * (T 0 N c hc * u * (T 0 N c hc)⁻¹) * T 0 N c hc := by group
    have hφ : ∑ i ∈ Finset.range (N - 1), entN (u : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1) =
        c * ∑ i ∈ Finset.range (N - 1),
          entN ((T 0 N c hc * u * (T 0 N c hc)⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1) := by
      conv_lhs => rw [e]
      rw [T_conj_val, sdg_conj c hc]
    rw [hφ, AddChar.mulShift_apply]

end GlobalTheory.BadCount.WtPsi

namespace GlobalTheory.BadCount

open Formalism.L2.SG.Pf.AllRowsWt Formalism.L2.SG.Pf.AllRowsTr GlobalTheory.BadCount.WtPsi

theorem wtOf_eUk_indep : ∀ (D : D7) (k : Fin 2) (ψ ψ' : AddChar (ZMod (D.host.g k)) ℂ), ψ ≠ 1 → ψ' ≠ 1 →
    ∀ f, wtOf D k (eUk D k ψ) f = wtOf D k (eUk D k ψ') f := by
  intro D k ψ ψ' h h' f
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨c, hc0, rfl⟩ := exists_shift ψ ψ' h h'
  have hconj : eUk D k (ψ.mulShift c) =
      MonoidAlgebra.single (T 0 D.R.r c hc0) 1 * eUk D k ψ * MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1 := by
    unfold eUk
    exact (eU_conj c hc0 ψ).symm
  have h1 : (eUk D k (ψ.mulShift c) * D.ntypes.eSer k f).coeff 1 = (eUk D k ψ * D.ntypes.eSer k f).coeff 1 := by
    rw [hconj]
    have e1 : MonoidAlgebra.single (T 0 D.R.r c hc0) 1 * eUk D k ψ * MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1 *
        D.ntypes.eSer k f = MonoidAlgebra.single (T 0 D.R.r c hc0) 1 * (eUk D k ψ * D.ntypes.eSer k f) *
        MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1 := by
      rw [mul_assoc _ (MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1) (D.ntypes.eSer k f), ← D.ntypes.eSer_central,
        mul_assoc, mul_assoc, mul_assoc]
    rw [e1, tau_conj]
  have h2 : (eUk D k (ψ.mulShift c)).coeff 1 = (eUk D k ψ).coeff 1 := by
    rw [hconj, tau_conj]
  unfold wtOf
  rw [h1, h2]

end GlobalTheory.BadCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTwistBaseOf
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OnCmp

theorem weil_twist_base_of : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (χ : (AE D)ˣ →* Circle) (ω : GlobalTheory.OnTies.WeilRep D i), GlobalTheory.OnCmp.IsWeilTw R i χ ω → ∀ (k : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) k x → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ω (1, k) f = ((χ x : Circle) : ℂ) • R.ωP i A.μ0 (1, k) f := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i χ ω hω k x hx f hf
  have h := GlobalTheory.TwistFactorProof.weil_ratio (_root_.GlobalTheory.WeilUniq.weilDatum_unique D) (GlobalTheory.WeilChange.exists_weilDatum_twist D)
    (hR.thP.ωP i A.μ0) hω (GlobalTheory.TwistFactorProof.isDetRoot_one _) hx hf
  rw [h]
  congr 2
  show _ * (R.mu0 _ x * χ x * (R.mu0 _ x * R.xi A.μ0 x)⁻¹) = χ x
  rw [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0) x]
  simp only [map_one, mul_inv_cancel, inv_one, one_mul, mul_one]
  rw [mul_comm (R.mu0 _ x), mul_inv_cancel_right]

end GlobalTheory.OnCmp
end

