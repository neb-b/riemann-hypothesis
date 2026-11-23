module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactQLat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SourceLiftAtGluedPlaceProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcGl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_mul_blk (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (g : GL n' k) (x : Matrix n (n' ⊕ Fin 1) k) :
    tensCol Ψ a (x * (blk g).val) = tensCol (fun x₀ => Ψ (x₀ * g.val)) a x := by
  simp only [tensCol, blk_val]
  congr 2
  · ext i j
    simp [Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type]
  · ext i
    simp [Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type]

theorem phiOne_smul_left (g : GL n' k) (P : Pair k n') (Q : Pair k n) (x : Matrix n n' k) :
    phiOne (g • P) Q x = phiOne P Q (x * g.val) := by
  classical
  have hs : ∀ (h : GL n' k) (y : n' → k), h • y = h.val *ᵥ y := fun _ _ => rfl
  unfold phiOne
  congr 1
  apply propext
  rw [maps_iff_hasVal, maps_iff_hasVal]
  constructor
  · intro h y a hy
    have := h (g • y) a (hy.gl_smul g)
    simpa [hs, Matrix.mulVec_mulVec] using this
  · intro h y a hy
    have := h (g⁻¹ • y) a (Pair.smul_hasVal.1 hy)
    simpa [hs, Matrix.mulVec_mulVec] using this

end GlobalTheory.FinPl.SrcGl

namespace GlobalTheory.FinPl.SrcGl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n' : Type} [Fintype n'] [DecidableEq n']

theorem coe_FFStar {A : HSp D} (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n' (CA A)) (P : Pair k n') :
    ((FFStar q χ φ P : CA A) : GA D A → ℂ) = FFStar q χ (fun P => (φ P : GA D A → ℂ)) P := by
  simp [FFStar_apply]

def toCA {A : HSp D} (φ : Form k n' (GA D A → ℂ)) (h : ∀ P, IsContAut A (φ P)) : Form k n' (CA A) :=
  fun P => ⟨φ P, h P⟩

theorem toCA_ram {A : HSp D} {α : Frame p A n'} {φ : Form k n' (GA D A → ℂ)} (hφ : IsRam α φ) :
    toCA φ hφ.2.2 ∈ Mram k n' (CA A) ∧ toCA φ hφ.2.2 ∈ EqForm (caRep α) := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  refine ⟨(mem_Mram _).2 fun P => Subtype.ext ?_, fun g P => Subtype.ext (hφ.1 g P)⟩
  simpa [toCA] using (mem_Mram φ).1 hφ.2.1 P

theorem exists_lat_eq (P : Pair k n') : ∃ P' : Pair k n', P'.lat = P.ker := by
  have h1 : Module.finrank 𝓀[k] (Red P.ker) = Module.finrank 𝓀[k] (Red P.lat) := by
    rw [Red.finrank_eq, Red.finrank_eq]
  have h2 : Nontrivial (Red P.lat) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact P.red_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  have h3 : 0 < Module.finrank 𝓀[k] (Red P.ker) := h1 ▸ Module.finrank_pos
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 h3
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual 𝓀[k] (Red P.ker), f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff 𝓀[k] x).1 h)
  exact ⟨ofDual P.ker ⟨f, fun h0 => hf (by rw [h0]; rfl)⟩, ofDual_lat _ _⟩

variable {n : Type} [Fintype n] [DecidableEq n]

def tensL (a : (n → k) → ℂ) : (Matrix n n' k → ℂ) →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) where
  toFun Ψ := tensCol Ψ a
  map_add' Ψ Ψ' := by ext x; simp [tensCol, add_mul]
  map_smul' c Ψ := by ext x; simp [tensCol, mul_assoc]

@[simp] theorem tensL_apply (a : (n → k) → ℂ) (Ψ : Matrix n n' k → ℂ) : tensL a Ψ = tensCol Ψ a := rfl

theorem tensCol_add (Ψ Ψ' : Matrix n n' k → ℂ) (a : (n → k) → ℂ) : tensCol (Ψ + Ψ') a = tensCol Ψ a + tensCol Ψ' a :=
  (tensL a).map_add Ψ Ψ'

end GlobalTheory.FinPl.SrcGl

open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl in
theorem GlobalTheory.FinPl.sourceGlued : ∀ D : D7, GlobalTheory.FinPl.SourceGlued D := by
  intro D k _ _ _ _ p n n' _ _ _ _ q χ₀ hχ χ hχχ ψ S A L T o ζ hL hA vA χS χT om hW _ hT α α₀ β hsum P P₁ Λ _
  obtain ⟨lS, hlS, hθ⟩ := _root_.GlobalTheory.FinPl.SrcTheta.exists_theta D k p n n' ψ S A L T o ζ hL hA vA χS χT om hW α α₀ β hsum
  have hdet : ∀ L' : Submodule 𝒪[k] (n' → k), L'.IsFullLattice k → ∀ g ∈ latStab L',
      ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 1 := fun L' hL' g hg => by
    rw [GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one k n' L' hL' g hg lS (hlS hT), Units.val_one]
  have hsb := GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts k n n'

  have hinv : ∀ (θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ)),
      (∀ (g : GL n' k) (v : CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) →
        θ (caRep α g v) (fun x => Φ (x * (blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ) →
      ∀ a ∈ SB (n → k), ∀ L' : Submodule 𝒪[k] (n' → k), L'.IsFullLattice k →
        GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.IsLiftInv (caRep α) (θ.compl₂ (tensL a)) L' := by
    intro θ hθe a ha L' hL' g hg v Ψ hΨ
    simp only [LinearMap.compl₂_apply, tensL_apply]
    have := hθe g v _ (hsb.1 Ψ a hΨ ha)
    rw [hdet L' hL' g hg, inv_one, one_smul] at this
    refine Eq.trans (congrArg _ ?_) this
    funext x
    exact (tensCol_mul_blk Ψ a g x).symm
  obtain ⟨P', hP'⟩ := exists_lat_eq P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n' k) P' P₁
  refine ⟨⟨((resCard k : ℂ) ^ Fintype.card n)⁻¹ * ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ), ?_⟩, ?_⟩
  · intro LS LT f₀ Ξ Ξ' hΞ hΞ' φ hφ
    obtain ⟨θ, hθv, hθe⟩ := hθ LS LT f₀ hΞ.1 hΞ.2.1 hΞ.2.2.1
    obtain ⟨hram, heq⟩ := toCA_ram hφ
    set φc := toCA φ hφ.2.2 with hφc
    have hχ1 : χ ≠ 1 := hχχ ▸ resChar_ne_one hχ q
    rw [show liftA o om vA (φ P) Ξ = θ (φc P) _ from (hθv (φc P) _ _ hΞ).symm,
      ((GlobalTheory.T.gluedLattice_finite_expansions_localField k n n' q χ hχ1 Λ).1 P).1]
    have e0 : θ (φc P) (tensCol (latInd P.ker Λ) (vecInd Λ)) = 0 :=
      GlobalTheory.LastSteps.lift_latInd P hram heq (hinv θ hθe _ (hsb.2.1 Λ inferInstance) P.ker inferInstance) Λ
    have e1 : ∀ Q ∈ withLat Λ, θ (φc P) (tensCol (latInd P.ker Q.ker + GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mainDatum q χ 1 P Q)
        (charInd χ Q)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • liftA o om vA (FFStar q χ φ P₁) (Ξ' Q) := by
      intro Q hQ
      have hI := hinv θ hθe _ (hsb.2.2 χ Q) P.ker inferInstance
      have a0 : θ (φc P) (tensCol (latInd P.ker Q.ker) (charInd χ Q)) = 0 :=
        GlobalTheory.LastSteps.lift_latInd P hram heq hI Q.ker
      have a1 := GlobalTheory.LastSteps.lift_mainDatum q χ 1 heq hI Q rfl hP'
      simp only [LinearMap.compl₂_apply, tensL_apply, map_one, Module.End.one_apply] at a1
      have a2 := hθe g⁻¹ (FFStar q χ φc P₁) _ (hΞ' Q hQ).2.2.2.1
      have b1 : caRep α g⁻¹ (FFStar q χ φc P₁) = FFStar q χ φc P' := by
        rw [← hg, FFStar_mem_EqForm q χ heq g P', ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
      have b2 : (fun x => tensCol (phiOne P₁ Q) (charInd χ Q) (x * (blk g⁻¹).val)) = tensCol (phiOne P' Q) (charInd χ Q) := by
        funext x
        rw [tensCol_mul_blk]
        congr 1
        funext x₀
        rw [← hg, phiOne_smul_left, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      rw [b1, b2, hθv _ _ _ (hΞ' Q hQ), coe_FFStar] at a2
      rw [tensCol_add, map_add (f := _), a0, zero_add, a1, a2, map_inv, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_add (f := _), map_sum, e0, zero_add, Finset.sum_congr rfl e1, ← Finset.smul_sum, smul_smul]
  · intro LS LT f₀ Ξ a hor φ hφ
    obtain ⟨L₁, hL₁, hO⟩ : ∃ L₁ : Submodule 𝒪[k] (n' → k), (L₁ = P.lat ∨ L₁ = P.ker) ∧
        Over ψ α₀ β LS LT f₀ (tensCol (latInd L₁ Λ) a) Ξ := by
      rcases hor with h | h
      exacts [⟨_, Or.inl rfl, h⟩, ⟨_, Or.inr rfl, h⟩]
    haveI : L₁.IsFullLattice k := by rcases hL₁ with rfl | rfl <;> infer_instance
    obtain ⟨θ, hθv, hθe⟩ := hθ LS LT f₀ hO.1 hO.2.1 hO.2.2.1
    obtain ⟨hram, heq⟩ := toCA_ram hφ
    set φc := toCA φ hφ.2.2 with hφc
    rw [show liftA o om vA (φ P) Ξ = θ (φc P) _ from (hθv (φc P) _ _ hO).symm]
    have hinvL : ∀ g ∈ latStab L₁, ∀ w, θ (caRep α g w) (tensCol (latInd L₁ Λ) a) = θ w (tensCol (latInd L₁ Λ) a) := by
      intro g hg w
      have := hθe g w _ hO.2.2.2.1
      rw [hdet L₁ inferInstance g hg, inv_one, one_smul] at this
      refine Eq.trans (congrArg _ ?_) this
      funext x
      rw [tensCol_mul_blk]
      congr 1
      funext x₀
      exact (GlobalTheory.LastSteps.latInd_mul hg Λ x₀).symm
    have hv : formOf (caRep α) P (evalEquiv (caRep α) P ⟨φc, heq⟩) = φc :=
      congrArg Subtype.val ((evalEquiv (caRep α) P).left_inv ⟨φc, heq⟩)
    exact (GlobalTheory.PairOp.vanishing q).invariant_eq_zero (caRep α) P (evalEquiv (caRep α) P ⟨φc, heq⟩) (hv.symm ▸ hram) _
      (θ.flip (tensCol (latInd L₁ Λ) a)) (by
        rcases hL₁ with rfl | rfl
        exacts [Or.inl fun g hg w => hinvL g hg w, Or.inr fun g hg w => hinvL g hg w])
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterTransferSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.SplitTransfer

theorem seg_map_inv {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : ℂˣ) (t : ℕ) :
    (GlobalTheory.LFun.seg w x t).map (·⁻¹) = GlobalTheory.LFun.seg w x⁻¹ t := by
  have hr : (Finset.range t).image (fun i => t - 1 - i) = Finset.range t := by
    ext i
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · intro hi; exact ⟨t - 1 - i, by omega, by omega⟩
  have hinj : Set.InjOn (fun i => t - 1 - i) (Finset.range t : Set ℕ) := fun a ha b hb e => by
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at e
    omega
  unfold GlobalTheory.LFun.seg
  conv_rhs => rw [← hr, Finset.image_val_of_injOn hinj, Multiset.map_map]
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  have hi' : i < t := Finset.mem_range.1 hi
  simp only [Function.comp_apply, mul_inv]
  congr 1
  apply Units.ext
  simp only [Units.val_inv_eq_inv_val, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow]
  rw [← Complex.cpow_neg]
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring


set_option maxHeartbeats 1600000 in
theorem transferOn_isSplit : ∀ D : D7, TransferOn D fun v => IsSplit (E := D.host.E) v := by
  intro D ψ S T χS χT om hW t ht v hv hunr w h U hU f hf X _ _ ρ x B hx X' _ _ ρ' b hb hne
  obtain ⟨eS, heS⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D S v w h).1 hv
  obtain ⟨eT, heT⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D T v w h).1 hv
  have hxS := hx.isSatVecGL hv heS
  obtain ⟨hfix, hH⟩ := GlobalTheory.T.latticeVacuum_heckeIdentity_splitPlace_charts D ψ S T χS χT om hW t ht v w h hv hunr eS eT heS heT (f : WO S T → ℂ) hf
  obtain ⟨hcS, hsS⟩ := GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm D.host.E w S.rank
  obtain ⟨hcT, hsT⟩ := GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm D.host.E w T.rank
  let σF : Representation ℂ (GL (Fin S.rank) (w.adicCompletion D.host.E)) (WO S T → ℂ) :=
    ((om.comp (MonoidHom.inl _ _)).comp (embV S v)).comp eS.symm.toMonoidHom
  let πF : Representation ℂ (GL (Fin T.rank) (w.adicCompletion D.host.E)) (WO S T → ℂ) :=
    ((om.comp (MonoidHom.inr _ _)).comp (embV T v)).comp eT.symm.toMonoidHom
  have eσ : ∀ g, σF g = om (embV S v (eS.symm g), embV T v 1) := fun g => by simp [σF]
  have eπ : ∀ g, πF g = om (embV S v 1, embV T v (eT.symm g)) := fun g => by simp [πF]
  let σU := σF.subrepresentation U fun g u hu => by rw [Submodule.mem_comap, eσ]; exact hU _ _ u hu
  let πU := πF.subrepresentation U fun g u hu => by rw [Submodule.mem_comap, eπ]; exact hU _ _ u hu
  let ρS := ρ.comp eS.symm.toMonoidHom
  let ρT := ρ'.comp eT.symm.toMonoidHom

  have hKS : ∀ k ∈ KGL w (n := S.rank), eS.symm k ∈ Kv S v := fun k hk => (heS.2 (eS.symm k)).2 (by simpa using hk)
  have hKT : ∀ k ∈ KGL w (n := T.rank), eT.symm k ∈ Kv T v := fun k hk => (heT.2 (eT.symm k)).2 (by simpa using hk)
  have hfS : f ∈ fixed σU (KGL w (n := S.rank)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
    change σF k (f : WO S T → ℂ) = f
    rw [eσ]; exact hfix _ (hKS k hk) _ (one_mem _))
  have hfT : f ∈ fixed πU (KGL w (n := T.rank)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
    change πF k (f : WO S T → ℂ) = f
    rw [eπ]; exact hfix _ (one_mem _) _ (hKT k hk))
  have hequiv : ∀ g (u : U), (b.flip x) (πU g u) = ρT g ((b.flip x) u) := fun g u => by
    have e := hb 1 (eT.symm g) u x
    rw [show ρ 1 x = x by simp] at e
    rw [LinearMap.flip_apply, LinearMap.flip_apply]
    change b (πU g u) x = ρ' (eT.symm g) (b u x)
    rw [← e]
    congr 2
    exact Subtype.ext (by change πF g (u : WO S T → ℂ) = _; rw [eπ])
  have hinv : ∀ g (u : U) y, b (σU g u) (ρS g y) = b u y := fun g u y => by
    have e := hb (eS.symm g) 1 u y
    rw [show ρ' 1 (b u y) = b u y by simp] at e
    rw [← e]
    congr 2
    exact Subtype.ext (by change σF g (u : WO S T → ℂ) = _; rw [eσ])
  have hbfix : b f x ∈ fixed ρT (KGL w (n := T.rank)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    have e := hequiv k f
    rw [GlobalTheory.LGrp.mem_fixed.1 hfT k hk] at e
    exact e.symm
  have hcard : (stepPar χS χT t (fun _ => B) w).card = T.rank := by
    simp [stepPar, GlobalTheory.LFun.seg, hxS.2.2.1, ht]
  have hB'inv : (stepPar χS χT t (fun _ => B) w).map (·⁻¹) =
      (B.map (·⁻¹)).map ((val (F := D.host.F) χS w)⁻¹ * ((val (F := D.host.F) χT w)⁻¹)⁻¹ * ·) +
        GlobalTheory.LFun.seg w (val (F := D.host.F) χS w)⁻¹ t := by
    rw [stepPar, Multiset.map_add (f := _), seg_map_inv, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun c _ => ?_
    simp only [Function.comp_apply, mul_inv]
  refine Or.inl ⟨hv, eT, heT, (GlobalTheory.T.satake_vector_iff_inverse_doubleCosets D.host.E w T.rank X' ρT (b f x) _ hne hbfix hcard).2 fun ϖ hϖ k hk => ?_⟩
  have hsubT : ∀ g (y : U), U.subtype (πU g y) = πF g (U.subtype y) := fun g y => rfl
  have hsubS : ∀ g (y : U), U.subtype (σU g y) = σF g (U.subtype y) := fun g y => rfl
  have hInvT : (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) ∈ Hecke ℂ (KGL w (n := T.rank)) :=
    (_root_.GlobalTheory.ChainOnto.heckeVec_move _ (KGL w (n := T.rank)) hcT hsT ℂ ℂ ℂ 1 1 0 (fun _ _ _ => by simp) 0 (zero_mem _) 0 (zero_mem _) _
      (Tj_mem_hecke hϖ k)).1
  let cf : ℕ → ℂ := fun j => if j ≤ k then (qV D.host.E w : ℂ) ^ ((S.rank - j) * (k - j)) *
    (Formalism.L2.Col.gaussBin (qV D.host.E w) t (k - j) : ℂ) *
    (((val (F := D.host.F) χS w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ S.rank)⁻¹ ^ k *
    (((val (F := D.host.F) χT w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ T.rank) ^ j else 0
  have hH' : heckeVec πF (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (U.subtype f) =
      ∑ j ∈ Finset.range (S.rank + 1), cf j • heckeVec σF (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) (U.subtype f) :=
    hH ϖ hϖ k hk
  have e1 : U.subtype (heckeVec πU (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f) =
      heckeVec πF (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (U.subtype f) :=
    map_heckeVec hcT hInvT U.subtype hsubT f
  have e2 : ∀ j, U.subtype (heckeVec σU (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f) =
      heckeVec σF (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) (U.subtype f) := fun j =>
    map_heckeVec hcS (Tj_mem_hecke hϖ j) U.subtype hsubS f
  have hT : heckeVec πU (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f =
      ∑ j ∈ Finset.range (S.rank + 1), cf j • heckeVec σU (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f := by
    apply U.injective_subtype
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, hH', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, e2 j]
  have hmove : ∀ j ∈ Finset.range (S.rank + 1), b (heckeVec σU (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f) x =
      satEig (qV D.host.E w) S.rank (B.map (·⁻¹)) j • b f x := by
    intro j hj
    rw [(_root_.GlobalTheory.ChainOnto.heckeVec_move _ _ hcS hsS U X X' σU ρS b hinv f hfS x hxS.2.1 _ (Tj_mem_hecke hϖ j)).2,
      (GlobalTheory.T.satake_vector_iff_inverse_doubleCosets D.host.E w S.rank X ρS x B hxS.1 hxS.2.1 hxS.2.2.1).1 hxS ϖ hϖ j
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), map_smul]
  have hsym := _root_.GlobalTheory.ChainOnto.satEig_map_add_seg D.host.E w S.rank t k (B.map (·⁻¹)) (val (F := D.host.F) χS w)⁻¹
    (val (F := D.host.F) χT w)⁻¹ (by rw [Multiset.card_map, hxS.2.2.1]) (ht ▸ hk)
  calc heckeVec ρT (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (b f x)
      = b (heckeVec πU (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f) x :=
        (map_heckeVec hcT hInvT (b.flip x) hequiv f).symm
    _ = ∑ j ∈ Finset.range (S.rank + 1), cf j • satEig (qV D.host.E w) S.rank (B.map (·⁻¹)) j • b f x := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hT, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [map_smul, LinearMap.smul_apply, hmove j hj]
    _ = satEig (qV D.host.E w) T.rank ((stepPar χS χT t (fun _ => B) w).map (·⁻¹)) k • b f x := by
        simp_rw [smul_smul]
        rw [← Finset.sum_smul]
        congr 1
        rw [hB'inv, ht, hsym]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        simp only [cf]
        split_ifs
        · rw [ht]
          simp only [Units.val_inv_eq_inv_val, inv_inv, mul_inv]
        · rfl

end GlobalTheory.ChainOnto.SplitTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalTransferWeilPairingInertPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto


set_option maxHeartbeats 1000000 in
theorem transferOn_inert : GlobalTheory.Hk3.HoweUnram → ∀ D : D7, TransferOn D fun v => ¬ IsSplit (E := D.host.E) v := by
  intro hH D ψ S T χS χT om hW t ht v hv hunr w h U hU f hf X _ _ ρ x B hx X' _ _ ρ' b hb hbne
  obtain ⟨hS, hT⟩ := hunr w h
  rcases hx with ⟨hs, -⟩ | ⟨hin, c, ϖ, eS, α, hUI, heS, hxS, rfl⟩
  · exact absurd hs hv
  obtain ⟨-, hodd, hch⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D T v w h).2 hv
  obtain ⟨eT, heT⟩ := hch c heS.1
  have hf0 : (f : WO S T → ℂ) ≠ 0 := fun h0 => hbne (by rw [show f = 0 from Subtype.ext h0]; simp)
  obtain ⟨δ, ψ', M, ρ0, ω, s, hstd, hsf, hωom, hcT, hcS⟩ :=
    _root_.GlobalTheory.ChainOnto.std_cayley_of_inert D ψ S T χS χT om hW v w h hin hS hT c ϖ eS eT hUI heS heT f hf hf0
  have hq0 : (qV D.host.F v : ℂ) ≠ 0 := by exact_mod_cast hodd.pos.ne'
  obtain ⟨hvS, hsegS⟩ := GlobalTheory.T.heckeChar_value_inert_place_and_segment D χS S.rank hW.hecS hW.resS v w h hin hS
  obtain ⟨hvT, -⟩ := GlobalTheory.T.heckeChar_value_inert_place_and_segment D χT T.rank hW.hecT hW.resT v w h hin hT
  refine Or.inr ⟨hin, c, ϖ, eT, liftPar (Units.mk0 _ hq0) S.rank T.rank α, hUI, heT, ?_, ?_⟩
  · set α' := liftPar (Units.mk0 _ hq0) S.rank T.rank α
    have e1S : embV S v (eS.symm 1) = 1 := by rw [map_one, map_one]
    have e1T : embV T v (eT.symm 1) = 1 := by rw [map_one, map_one]
    have e0S : embV S v 1 = 1 := map_one _
    have e0T : embV T v 1 = 1 := map_one _
    obtain ⟨RS, hRS⟩ : ∃ RS : Representation ℂ (GU c S.rank) (WO S T → ℂ),
        ∀ g u, RS g u = om (embV S v (eS.symm g), 1) u :=
      ⟨om.comp ((MonoidHom.inl _ _).comp ((embV S v).comp eS.symm.toMonoidHom)), fun _ _ => rfl⟩
    obtain ⟨RT, hRT⟩ : ∃ RT : Representation ℂ (GU c T.rank) (WO S T → ℂ),
        ∀ g u, RT g u = om (1, embV T v (eT.symm g)) u :=
      ⟨om.comp ((MonoidHom.inr _ _).comp ((embV T v).comp eT.symm.toMonoidHom)), fun _ _ => rfl⟩
    obtain ⟨πS, hπS⟩ : ∃ πS : Representation ℂ (GU c S.rank) U, ∀ g (u : U), ((πS g u : U) : WO S T → ℂ) = RS g u :=
      ⟨GlobalTheory.PRep.sub RS U fun g u hu => by rw [hRS, ← e0T]; exact hU _ _ u hu, fun _ _ => rfl⟩
    obtain ⟨πT, hπT⟩ : ∃ πT : Representation ℂ (GU c T.rank) U, ∀ g (u : U), ((πT g u : U) : WO S T → ℂ) = RT g u :=
      ⟨GlobalTheory.PRep.sub RT U fun g u hu => by rw [hRT, ← e0S]; exact hU _ _ u hu, fun _ _ => rfl⟩
    have hMS : ∀ g (m : M), ((ω (g, 1) m : M) : WO S T → ℂ) = RS g m := fun g m => by
      rw [hRS, hωom, e1T]
    have hMT : ∀ g (m : M), ((ω (1, g) m : M) : WO S T → ℂ) = RT g m := fun g m => by
      rw [hRT, hωom, e1S]
    have hvac := hstd.2.2.1
    have hfixS : ∀ k ∈ KU c S.rank, πS k f = f := fun k hk => by
      have a4 := hstd.1.fix k 1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2 (one_mem _) s hvac
      apply Subtype.ext
      rw [hπS, ← hsf, ← hMS]; exact congrArg Subtype.val a4
    have hfixT : ∀ k ∈ KU c T.rank, πT k f = f := fun k hk => by
      have a4 := hstd.1.fix 1 k (one_mem _) (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2 s hvac
      apply Subtype.ext
      rw [hπT, ← hsf, ← hMT]; exact congrArg Subtype.val a4
    have hcom1 := _root_.GlobalTheory.ChainOnto.inert_cosetSym_heckeEven _ ϖ c _ hUI S.rank
    have hcom2 := _root_.GlobalTheory.ChainOnto.inert_cosetSym_heckeEven _ ϖ c _ hUI T.rank
    have hρ1 : ρ 1 x = x := by rw [map_one]; rfl
    have hbT : ∀ g (u : U), b (πT g u) x = ρ' (eT.symm g) (b u x) := fun g u => by
      have e2 := hb 1 (eT.symm g) u x
      have e : πT g u = ⟨om (embV S v 1, embV T v (eT.symm g)) u, hU _ _ u u.2⟩ :=
        Subtype.ext ((hπT g u).trans ((hRT g u).trans (congrArg (fun z => om (z, embV T v (eT.symm g)) (u : WO S T → ℂ)) e0S.symm)))
      rw [hρ1] at e2
      rw [e, e2]
    have hbS : ∀ g (u : U) y, b (πS g u) (ρ (eS.symm g) y) = b u y := fun g u y => by
      have e2 := hb (eS.symm g) 1 u y
      have e : πS g u = ⟨om (embV S v (eS.symm g), embV T v 1) u, hU _ _ u u.2⟩ :=
        Subtype.ext ((hπS g u).trans ((hRS g u).trans (congrArg (fun z => om (embV S v (eS.symm g), z) (u : WO S T → ℂ)) e0T.symm)))
      rw [map_one ρ', Module.End.one_apply] at e2
      rw [e, e2]
    refine ⟨hbne, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun h' hh' => ?_⟩
    · show ρ' (eT.symm k) (b f x) = b f x
      rw [← hbT, hfixT k hk]
    · have : CharZero (w.adicCompletion D.host.E) :=
        charZero_of_injective_algebraMap (algebraMap D.host.E (w.adicCompletion D.host.E)).injective
      obtain ⟨h0, hh0, heq⟩ := _root_.GlobalTheory.ChainOnto.heckeVec_howe hH _ ϖ c _ δ ψ' S.rank T.rank M ρ0 ω s hstd h' hh'
      have hsat := _root_.GlobalTheory.SphTheta.satU_eq_satU_liftPar_of_heckeVec_eq _ ϖ c _ δ ψ' S.rank T.rank M ρ0 ω s hstd hcT hcS (by omega) h0 hh0 h' hh' heq
        (Units.mk0 _ hq0) rfl α
      have sA : b (heckeVec πT (KU c T.rank) h' f) x =
          heckeVec (ρ'.comp eT.symm.toMonoidHom) (KU c T.rank) h' (b f x) :=
        map_heckeVec hcom2.1 hh' (b.flip x) (fun g u => hbT g u) f
      have sB : heckeVec πT (KU c T.rank) h' f = heckeVec πS (KU c S.rank) h0 f := by
        apply Subtype.ext
        have m1 := map_heckeVec hcom2.1 hh' U.subtype (ρ' := RT) (fun g u => hπT g u) f
        have m2 := map_heckeVec hcom2.1 hh' M.subtype (ρ := ω.comp (MonoidHom.inr _ _)) (ρ' := RT) (fun g m => hMT g m) s
        have m3 := map_heckeVec hcom1.1 hh0 M.subtype (ρ := ω.comp (MonoidHom.inl _ _)) (ρ' := RS) (fun g m => hMS g m) s
        have m4 := map_heckeVec hcom1.1 hh0 U.subtype (ρ' := RS) (fun g u => hπS g u) f
        simp only [Submodule.subtype_apply] at m1 m2 m3 m4
        rw [m1, m4, ← hsf, ← m2, ← m3, heq]
      have sC := (_root_.GlobalTheory.ChainOnto.heckeVec_move (GU c S.rank) (KU c S.rank) hcom1.1 hcom1.2.1 U X X' πS (ρ.comp eS.symm.toMonoidHom) b
        (fun g u y => hbS g u y) f (GlobalTheory.LGrp.mem_fixed.2 hfixS) x hxS.2.1 h0 hh0).2
      have hev : (fun g => h0 g⁻¹) = h0 := funext fun g => hcom1.2.2 h0 hh0 g
      rw [← sA, sB, sC, hev, hxS.2.2 h0 hh0, map_smul, hsat]
  · have hc := GlobalTheory.T.baseChange_thetaLiftSatakeParameter_eq_add_segment (Units.mk0 _ hq0) S.rank T.rank (by omega) α
    have ht' : ((T.rank : ℤ) - S.rank) = (t : ℤ) := by omega
    rw [ht'] at hc
    have e := congrArg (Multiset.map (((-1 : ℂˣ) ^ S.rank) * ·)) hc
    simp only [Multiset.map_map, Multiset.map_add (f := _), Function.comp_def, mul_inv_cancel_left] at e
    rw [Multiset.map_id'] at e
    rw [e, stepPar, hvS, hvT, hsegS (Units.mk0 _ hq0) _ t rfl]
    congr 1
    · exact Multiset.map_congr rfl fun y _ => by group

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHomLatticeCompletionOpenCompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_homLattice_completion_openCompact : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T), Submodule.IsFullLattice D.host.E LS → Submodule.IsFullLattice D.host.E LT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y), IsOpen (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) ∧ IsCompact (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) := by
  intro D k _ _ _ _ p S T LS LT hLS hLT
  letI := hLS
  letI := hLT
  exact GlobalTheory.OpenCompactLat.openCompact D k p S T LS LT inferInstance inferInstance
end

