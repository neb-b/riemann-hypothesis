module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormOnHomsReframeHomMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.Sympl

theorem quad_sum_eq_trace {A : Type} [CommRing A] {m n : ℕ} (H : Matrix (Fin n) (Fin n) A)
    (G : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * y c b * G c d * x d a = Matrix.trace (H * (yᵀ * (G * x))) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem trace_change {A : Type} [CommRing A] {m n : ℕ} (H Q Q' : Matrix (Fin n) (Fin n) A)
    (G : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    Matrix.trace ((Q * (H * Q'ᵀ)) * (yᵀ * (G * x))) = Matrix.trace (H * ((y * Q')ᵀ * (G * (x * Q)))) := by
  rw [Matrix.transpose_mul]
  have hre : H * (Q'ᵀ * yᵀ * (G * (x * Q))) = (H * Q'ᵀ * yᵀ * G * x) * Q := by
    simp only [Matrix.mul_assoc]
  rw [hre, Matrix.trace_mul_comm (H * Q'ᵀ * yᵀ * G * x) Q]
  simp only [Matrix.mul_assoc]

variable {D : D7}

theorem gram_reS (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from HSpace.gram (reS S b))
      = (frP S b)ᴴ * HSpace.gram S * frP S b := by
  have hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l := fun k => by
    simp only [frP, Module.Basis.toMatrix_apply]
    exact (S.frame.sum_repr (b k)).symm
  ext i j
  change S.hT (b i) (b j) = _
  rw [hb i, hb j]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  simp only [HSpace.gram, RingHom.id_apply, starRingEnd_apply]
  ring

theorem gram_reS_inv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from HSpace.gram (reS S b))⁻¹
      = frPinv S b * ((HSpace.gram S)⁻¹ * (frPinv S b)ᴴ) := by
  have h := gram_reS S b
  dsimp only at h ⊢
  rw [h, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv,
    Matrix.inv_eq_left_inv (frPinv_mul_frP S b)]

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (((HSpace.gram S)⁻¹).map (incA D) *
      ((Matrix.map (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from y) (cA D))ᵀ *
        ((HSpace.gram T).map (incA D) * (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from x)))) := by
  unfold hO
  dsimp only
  refine Eq.trans ?_ (quad_sum_eq_trace _ _ _ _)
  simp only [Matrix.map_apply]

theorem hO_reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x y : WO (reS S b) T) :
    hO (reS S b) T x y = hO S T (reW S T b x) (reW S T b y) := by
  have hP : (frPinv S b * ((HSpace.gram S)⁻¹ * (frPinv S b)ᴴ)).map (incA D) =
      (frPinv S b).map (incA D) * ((HSpace.gram S)⁻¹.map (incA D) *
        (((frPinv S b).map (incA D)).map (cA D))ᵀ) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 2
  have hi := gram_reS_inv S b
  dsimp only at hi
  have key := trace_change ((HSpace.gram S)⁻¹.map (incA D)) ((frPinv S b).map (incA D))
    (((frPinv S b).map (incA D)).map (cA D)) ((HSpace.gram T).map (incA D)) x (y.map (cA D))
  rw [← hP, ← hi] at key
  rw [hO_eq_trace, hO_eq_trace]
  dsimp only
  refine key.trans ?_
  clear key hi hP
  unfold reW
  have hm : (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) y ((frPinv S b).map (incA D))).map (cA D) =
      Matrix.map (α := AE D) (m := Fin T.rank) (n := Fin S.rank) y (cA D) * ((frPinv S b).map (incA D)).map (cA D) :=
    Matrix.map_mul
  exact congrArg (fun M => ((HSpace.gram S)⁻¹.map (incA D) *
    (Mᵀ * ((HSpace.gram T).map (incA D) *
      HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))))).trace) hm.symm

theorem symplO_reW : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x y : WO (reS S b) T),
    symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y) := by
  intro D S T b x y
  unfold symplO
  rw [hO_reW]

end GlobalTheory.AdSpan.ReVec.Sympl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepCentredBlockParameters
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare GlobalTheory.Chain.ParOfSizes GlobalTheory.Chain.ParOfNodeGap

namespace GlobalTheory.ArchRec.ParChain

theorem num_bound_two {n q m N : ℕ} (hq : q ≤ m) (hn : n ≤ N) (hm : 1 ≤ m) (hN : 8 * m ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (N : ℝ) ^ 3 := by
  have hq' : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : 8 * (m : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    calc (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) := by gcongr
      _ ≤ (m : ℝ) ^ ((2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hm' (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_natCast _ _
  have h2 : 60 * (m : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (m : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) * (60 * (m : ℝ) ^ 2) := by ring
    _ ≤ 2 * (N : ℝ) * (N : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) ^ 3 := by ring

theorem stepGap_of_gap {D : D7} (h : NodeGap D) (k : Fin D.R.m) : StepGap D k := by
  intro τ
  obtain ⟨N, hN, hgap⟩ := h
  set h₀ : ℝ := (D.R.t : ℝ) + 2 * (N : ℝ) ^ 3 + 1 with hh
  have hg : ∀ (i : ℕ) (h : i + 1 < D.R.m),
      h₀ ≤ (((D.hc τ).b ⟨i + 1, h⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ) := by
    intro i h
    have := hgap τ ⟨i, by omega⟩ h
    rw [hh]
    exact_mod_cast this
  have hS : NcGapGe (lamS D k τ) h₀ := by
    rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hs
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ _ _).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ _ _).1 hy
    exact le_val_sub _ hg _ _ a b hs
  have hT : NcGapGe (lamT D k τ) h₀ := by
    rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hs
    obtain ⟨a, rfl, rfl⟩ := (mem_lamT k τ _ _).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamT k τ _ _).1 hy
    exact le_val_sub _ hg _ _ a b hs
  have hr : ∀ j, j ≤ D.R.m → D.R.rankY j ≤ N := fun j hj => by
    have := Nat.mul_le_mul_right D.R.t hj
    unfold Ranks.rankX' at hN
    unfold Ranks.rankY
    omega
  have h3 : 8 * D.R.m ≤ N := by
    have h8 : 8 ≤ D.R.t := by
      have := D.R.rank_add_five_le; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    have := Nat.mul_le_mul_left D.R.m h8
    unfold Ranks.rankX' at hN
    omega
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  have h1 : (D.R.rankY ((k : ℕ) + 1) : ℝ) ^ 3 < h₀ := by
    have h2 : (D.R.rankY ((k : ℕ) + 1) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hr _ k.2
    have h3 := pow_le_pow_left₀ (by positivity) h2 3
    have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
    linarith
  have h2 := num_bound_two (minSig_lamS_le k τ) (hr _ k.2.le) (by have := D.R.two_le_m; omega) h3
  exact ⟨fun x hx y hy hs => h1.trans_le (hS x hx y hy hs), fun x hx y hy hs => h1.trans_le (hT x hx y hy hs),
    fun x hx y hy hs => le_trans (by linarith) (hS x hx y hy hs)⟩

theorem parChain : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau), ∃ al be ga de : List ℚ, Centred D al be ga de ∧ parA (Ptw D) k τ = signed (al ++ be) (ga ++ de) (alT D k τ) ∧ parA (Ptw D) (k + 1) τ = signed (al ++ block D.R.t ++ de) (ga ++ be) (alS D k τ) := by
  intro D k τ
  obtain ⟨al, be, ga, de, hA, hb, h1, h2⟩ := exists_lists_chain k τ
  refine ⟨al, be, ga, de, ⟨hA, hb, fun hG => ?_⟩, eq_signed_iff.2 h1, eq_signed_iff.2 h2⟩
  have h := stepGap_of_gap hG k τ
  have hr : D.R.rankY ((k : ℕ) + 1) = D.R.rankY k + D.R.t := by simp only [Ranks.rankY]; ring
  rw [hr] at h
  refine (hypG_iff hA.2.2.2.2.2.2.1 (h1 ▸ card_lamS k τ)).2 ?_
  rwa [← h1, ← h2]

end GlobalTheory.ArchRec.ParChain

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralDefiniteSourceConvergesContinuousIn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.DefSourceInt

theorem theta_integral_source_definite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S W : HSp D) (χS χW : (AE D)ˣ →* Circle) (ω : WRep S W) (μ : Measure (GA D S)) (𝓕 : Set (GA D S)) (f : WO S W → ℂ), IsWeil ψ ε S W χS χW ω → (∀ τ, (gramAt D S τ).PosDef) → μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ → IsThetaFunO ψ (sgn ε S) W f → (∀ h, IntegrableOn (fun g => thetaKO ω g h f) 𝓕 μ) ∧ (Continuous fun h => ∫ g in 𝓕, thetaKO ω g h f ∂μ) ∧ ∀ γ ∈ GQ W, ∀ h, ∫ g in 𝓕, thetaKO ω g (γ * h) f ∂μ = ∫ g in 𝓕, thetaKO ω g h f ∂μ := by
  intro D ψ ε S W χS χW ω μ 𝓕 f hω hpos hμ h𝓕 hf
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  obtain ⟨hcont, hinv⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ (sgn ε S) W χS χW (WRep.toSgn ε ω) hω f hf
  have hK : ∀ g h, thetaKO ω g h f = thetaKO (WRep.toSgn ε ω) ((ofSgn ε S).symm g) h f := fun _ _ => rfl
  have hKc : Continuous fun p : GA D S × GA D W => thetaKO ω p.1 p.2 f :=
    (hcont.comp (((continuous_ofSgn_symm ε S).comp continuous_fst).prodMk continuous_snd)).congr fun p => (hK p.1 p.2).symm
  have hI : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ W, ∀ g h, thetaKO ω (γ * g) (γ' * h) f = thetaKO ω g h f := by
    intro γ hγ γ' hγ' g h
    rw [hK, hK, map_mul]
    exact hinv _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ ε hγ) γ' hγ' _ _
  have hIS : ∀ γ ∈ GQ S, ∀ g h, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g h => by
    have := hI γ hγ 1 (one_mem _) g h
    rwa [one_mul] at this
  have hIW : ∀ γ ∈ GQ W, ∀ g h, thetaKO ω g (γ * h) f = thetaKO ω g h f := fun γ hγ g h => by
    have := hI 1 (one_mem _) γ hγ g h
    rwa [one_mul] at this
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  refine ⟨fun h => ?_, ?_, fun γ hγ h => ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain S μ 𝓕 C hμ h𝓕 hC hcov _
      (hKc.comp (Continuous.prodMk_left h)) (fun γ hγ g => hIS γ hγ g h)
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) μ 𝓕 C h𝓕 hC hcov
      (fun h g => thetaKO ω g h f) (hKc.comp continuous_swap) (fun γ hγ h g => hIS γ hγ g h)
  · have e : (fun g => thetaKO ω g (γ * h) f) = fun g => thetaKO ω g h f := funext fun g => hIW γ hγ g h
    exact congrArg (fun F : GA D S → ℂ => ∫ g in 𝓕, F g ∂μ) e

end GlobalTheory.DefSourceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslNBPreserves
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.HaarCoords

theorem transl_nB_preserves : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (UX D ρ)) (lB : Measure (Mx D ρ S₀.rank)) (lC : Measure (skewA D ρ)), μ.IsHaarMeasure → lB.IsAddHaarMeasure → lC.IsAddHaarMeasure → SFinite μ → SFinite lB → SFinite lC → ∀ b' : Mx D ρ S₀.rank, ∃ T : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) → UX D ρ × (Mx D ρ S₀.rank × skewA D ρ), MeasurePreserving T (μ.prod (lB.prod lC)) (μ.prod (lB.prod lC)) ∧ ∀ p, d.levi (T p).1.1 * (d.nB (T p).2.1 * d.nC (T p).2.2) = d.nB b' * (d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) := by
  intro D S S₀ ρ d μ lB lC hμ hB hC _ _ _ b'
  obtain ⟨hTR, _, _, hSC, hBor⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI := hμ; haveI := hB; haveI := hC; haveI := hTR; haveI := hSC; haveI := hBor
  haveI hMxB : ∀ m n : ℕ, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
  haveI hMxS : ∀ m n : ℕ, SecondCountableTopology (Mx D m n) := fun m n =>
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AE D))
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩

  let v : UX D ρ → Mx D ρ S₀.rank := fun u => ((u.1)⁻¹ : GL (Fin ρ) (AE D)).1 ⬝ b'
  refine ⟨fun p => (p.1, (v p.1 + p.2.1, cComm S₀ (v p.1) p.2.1 + p.2.2)), ?_, ?_⟩
  · have hvm : Measurable v := by
      have hinv : Continuous fun u : UX D ρ => (((u.1)⁻¹ : GL (Fin ρ) (AE D)) : Matrix (Fin ρ) (Fin ρ) (AE D)) :=
        Units.continuous_coe_inv.comp continuous_subtype_val
      exact (hinv.matrix_mul continuous_const).measurable

    have hplus : Continuous fun b : Mx D ρ S₀.rank => plus S₀ b := by
      show Continuous fun b : Mx D ρ S₀.rank => giA S₀ ⬝ adj b
      exact continuous_const.matrix_mul continuous_adj
    have hΦ : Measurable fun q : Mx D ρ S₀.rank × Mx D ρ S₀.rank => ((cComm S₀ q.1 q.2 : skewA D ρ) : Mx D ρ ρ) := by
      have h1 : Continuous fun q : Mx D ρ S₀.rank × Mx D ρ S₀.rank => q.2 ⬝ plus S₀ q.1 :=
        continuous_snd.matrix_mul (hplus.comp continuous_fst)
      have h2 : Continuous fun q : Mx D ρ S₀.rank × Mx D ρ S₀.rank => q.1 ⬝ plus S₀ q.2 :=
        continuous_fst.matrix_mul (hplus.comp continuous_snd)
      have hc : Continuous fun q : Mx D ρ S₀.rank × Mx D ρ S₀.rank =>
          half D • (q.2 ⬝ plus S₀ q.1 - q.1 ⬝ plus S₀ q.2) :=
        (continuous_const_smul (half D)).comp (h1.sub h2)
      exact hc.measurable
    have hg : Measurable fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) =>
        ((v p.1 + p.2.1, cComm S₀ (v p.1) p.2.1 + p.2.2) : Mx D ρ S₀.rank × skewA D ρ) := by
      refine ((hvm.comp measurable_fst).add (measurable_fst.comp measurable_snd)).prodMk ?_
      exact Measurable.subtype_mk (f := fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) =>
          ((cComm S₀ (v p.1) p.2.1 : skewA D ρ) : Mx D ρ ρ) + (p.2.2 : Mx D ρ ρ))
        (h := fun p => (cComm S₀ (v p.1) p.2.1 + p.2.2).2)
        ((hΦ.comp ((hvm.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))).add
          (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)))
    have hfib : ∀ u : UX D ρ, Measure.map (fun q : Mx D ρ S₀.rank × skewA D ρ =>
        ((v u + q.1, cComm S₀ (v u) q.1 + q.2) : Mx D ρ S₀.rank × skewA D ρ)) (lB.prod lC) = lB.prod lC := by
      intro u
      have hk : Measurable fun q : Mx D ρ S₀.rank × skewA D ρ => (cComm S₀ (v u) q.1 + q.2 : skewA D ρ) :=
        Measurable.subtype_mk (f := fun q : Mx D ρ S₀.rank × skewA D ρ =>
            ((cComm S₀ (v u) q.1 : skewA D ρ) : Mx D ρ ρ) + (q.2 : Mx D ρ ρ))
          (h := fun q => (cComm S₀ (v u) q.1 + q.2).2)
          ((hΦ.comp (measurable_const.prodMk measurable_fst)).add (measurable_subtype_coe.comp measurable_snd))
      exact ((measurePreserving_add_left lB (v u)).skew_product (g := fun b (c : skewA D ρ) => cComm S₀ (v u) b + c) hk
        (Filter.Eventually.of_forall fun b => map_add_left_eq_self lC _)).map_eq
    exact (MeasurePreserving.id μ).skew_product
      (g := fun (u : UX D ρ) (q : Mx D ρ S₀.rank × skewA D ρ) => ((v u + q.1, cComm S₀ (v u) q.1 + q.2) : Mx D ρ S₀.rank × skewA D ρ))
      hg (Filter.Eventually.of_forall hfib)
  · rintro ⟨u, b, c⟩
    show d.levi u.1 * (d.nB (v u + b) * d.nC (cComm S₀ (v u) b + c)) = d.nB b' * (d.levi u.1 * (d.nB b * d.nC c))
    have hv : u.1.1 ⬝ v u = b' := by
      show u.1.1 ⬝ (((u.1)⁻¹ : GL (Fin ρ) (AE D)).1 ⬝ b') = b'
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [d.nC_add, ← mul_assoc (d.nB _), ← d.nB_mul_nB, ← mul_assoc, ← mul_assoc, d.levi_mul_nB, hv, mul_assoc, mul_assoc]

end GlobalTheory.HaarCoords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslNC
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.HaarCoords

theorem transl_nC : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (UX D ρ)) (lB : Measure (Mx D ρ S₀.rank)) (lC : Measure (skewA D ρ)), μ.IsHaarMeasure → lB.IsAddHaarMeasure → lC.IsAddHaarMeasure → SFinite μ → SFinite lB → SFinite lC → ∀ c' : skewA D ρ, ∃ T : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) → UX D ρ × (Mx D ρ S₀.rank × skewA D ρ), MeasurePreserving T (μ.prod (lB.prod lC)) (μ.prod (lB.prod lC)) ∧ ∀ p, d.levi (T p).1.1 * (d.nB (T p).2.1 * d.nC (T p).2.2) = d.nC c' * (d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) := by
  intro D S S₀ ρ d μ lB lC _ _ hC _ _ _ c'
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨i1, -, i3, -⟩ := lattice_Mx D ρ ρ
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : MeasurableAdd₂ (skewA D ρ) := inferInstance
  haveI : MeasurableAdd (skewA D ρ) := inferInstance
  let s : UX D ρ → skewA D ρ := fun u => skewConj (u⁻¹).1.1 c'
  have hinv : Continuous fun u : UX D ρ => (u⁻¹).1.1 := Units.continuous_coe_inv.comp continuous_subtype_val
  have hs : Continuous s := by
    refine Continuous.subtype_mk ?_ _
    exact (hinv.matrix_mul continuous_const).matrix_mul (continuous_adj.comp hinv)
  refine ⟨fun p => (p.1, (p.2.1, s p.1 + p.2.2)), ?_, ?_⟩
  · have hg : Measurable (Function.uncurry fun (u : UX D ρ) (q : Mx D ρ S₀.rank × skewA D ρ) => (q.1, s u + q.2)) :=
      measurable_snd.fst.prodMk ((hs.measurable.comp measurable_fst).add measurable_snd.snd)
    exact (MeasurePreserving.id μ).skew_product hg
      (Filter.Eventually.of_forall fun u => ((MeasurePreserving.id lB).prod (measurePreserving_add_left lC (s u))).map_eq)
  · rintro ⟨u, b, c⟩
    have h := d.levi_mul_nC c' (u⁻¹).1
    have hL : d.levi (u⁻¹).1 = (d.levi u.1)⁻¹ := by rw [Subgroup.coe_inv, map_inv]
    rw [hL] at h
    have h2 : d.nC c' * d.levi u.1 = d.levi u.1 * d.nC (s u) := by
      calc d.nC c' * d.levi u.1 = d.levi u.1 * ((d.levi u.1)⁻¹ * d.nC c') * d.levi u.1 := by rw [mul_inv_cancel_left]
        _ = d.levi u.1 * (d.nC (s u) * (d.levi u.1)⁻¹) * d.levi u.1 := by rw [h]
        _ = d.levi u.1 * d.nC (s u) := by rw [← mul_assoc (d.levi u.1), inv_mul_cancel_right]
    show d.levi u.1 * (d.nB b * d.nC (s u + c)) = d.nC c' * (d.levi u.1 * (d.nB b * d.nC c))
    rw [d.nC_add, ← mul_assoc (d.nC c'), h2, mul_assoc, ← mul_assoc (d.nC (s u)), d.nC_mul_nB, mul_assoc]

end GlobalTheory.HaarCoords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryRationalDiagonalHomBijective
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TwistRatBij

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem inclR_eq (e : E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F e = (Algebra.TensorProduct.lid F E).symm e := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.lid_symm_apply]

theorem inclR_lid (x : F ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F (Algebra.TensorProduct.lid F E x) = x := by
  rw [inclR_eq]; exact (Algebra.TensorProduct.lid F E).symm_apply_apply x

theorem lid_inclR (e : E) :
    Algebra.TensorProduct.lid F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F e) = e := by
  rw [inclR_eq]; exact (Algebra.TensorProduct.lid F E).apply_symm_apply e

theorem lid_sigR (σ : E →ₐ[F] E) (x : F ⊗[F] E) :
    σ (Algebra.TensorProduct.lid F E x) =
      Algebra.TensorProduct.lid F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

abbrev matOf {R : Type} [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA R σ J) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (((show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR R σ J from x) : GL (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E))

theorem diagH_val (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : Formalism.UG.UJ (σ : E →+* E) J) (i j : Fin n) :
    matOf (diagH σ J F g) i j =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F (((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) := rfl

theorem diagH_bijective : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), Function.Bijective (diagH σ J F) := by
  intro F E _ _ _ σ n J
  constructor
  · intro g h hgh
    apply Subtype.ext; apply Units.ext; ext i j
    have h1 := congrArg (fun x => matOf x i j) hgh
    simp only [diagH_val] at h1
    have h2 := congrArg (Algebra.TensorProduct.lid F E) h1
    rwa [lid_inclR, lid_inclR] at h2
  · intro h
    let h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR F σ J := h
    let L : F ⊗[F] E →+* E := (Algebra.TensorProduct.lid F E).toRingEquiv.toRingHom
    let g : GL (Fin n) E := Formalism.UG.bc L h'.1
    have hL : ∀ x, (σ : E →+* E) (L x) = L (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ x) := fun x => lid_sigR σ x
    have hmem : g ∈ Formalism.UG.UJ (σ : E →+* E) J := by
      have hh : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ) ((h'.1 : GL (Fin n) (F ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (F ⊗[F] E)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J *
          ((h'.1 : GL (Fin n) (F ⊗[F] E)) : Matrix (Fin n) (Fin n) (F ⊗[F] E)) =
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J := h'.2
      have hJ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J).map L = J := by
        ext r s; exact lid_inclR (J r s)
      show Formalism.UG.cT (σ : E →+* E) ((h'.1 : Matrix (Fin n) (Fin n) (F ⊗[F] E)).map L) * J *
        ((h'.1 : Matrix (Fin n) (Fin n) (F ⊗[F] E)).map L) = J
      generalize ((h'.1 : GL (Fin n) (F ⊗[F] E)) : Matrix (Fin n) (Fin n) (F ⊗[F] E)) = M at hh ⊢
      rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ) (σ : E →+* E) L hL, ← hJ,
        ← Matrix.map_mul, ← Matrix.map_mul, hh]
    refine ⟨⟨g, hmem⟩, ?_⟩
    apply Subtype.ext; apply Units.ext; ext i j
    exact inclR_lid _

end GlobalTheory.TwistRatBij
end

