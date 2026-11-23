module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefLiftMult

open Matrix

theorem sig_of_posDef {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) {p q : ℕ}
    (h : Formalism.UG.HasSignature G p q) : (p, q) = (n, 0) := by
  obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
  have hq : q = 0 := by
    by_contra hq
    have j : Fin q := ⟨0, Nat.pos_of_ne_zero hq⟩
    have h1 := (hG.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inr j)
    rw [hQ] at h1
    simp [Formalism.UG.Jpq] at h1
    exact absurd h1 (by norm_num)
  subst hq
  simp at hn
  rw [hn]

theorem exists_tauE (D : D7) (σ : D.host.E →+* ℂ) :
    ∃ τ, σ = tauE D τ ∨ σ = (starRingEnd ℂ).comp (tauE D τ) := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have key : ∀ (t : D.R.GG) (ht : t ∈ D.R.Psi),
      tauE D (D.eTau.symm ⟨t, ht⟩) = D.host.emb t := fun t ht => by
    unfold tauE
    rw [Equiv.apply_symm_apply]
  by_cases h : g ∈ D.R.Psi
  · exact ⟨D.eTau.symm ⟨_, h⟩, Or.inl (key g h).symm⟩
  · have h' : g * D.R.cc ∈ D.R.Psi := by
      by_contra h2
      exact h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h2)
    refine ⟨D.eTau.symm ⟨_, h'⟩, Or.inr ?_⟩
    rw [key, Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have := D.host.conjE_apply (D.host.emb g) x
    exact ((starRingEnd_self_apply _).symm.trans (congrArg (starRingEnd ℂ) this.symm))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem isDefinite (hs : V.SigOK) (h : AllPlus M) : V.IsDefinite := by
  intro σ
  refine Or.inl (sig_of_posDef ?_ (hs σ))
  obtain ⟨τ, rfl | rfl⟩ := exists_tauE D σ
  · exact h.posDef τ
  · have e : V.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (gramAt D V τ)ᴴᵀ := by
      ext i j
      rfl
    rw [e]
    exact (h.posDef τ).conjTranspose.transpose

theorem rTr_mem {θ : InfFam D} (hθ : IsInfFam θ) (U : Set (GA D V → ℂ))
    (hU : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ U, rTr V (atTau θ V τ g) f ∈ U) {k : GA D V}
    (hk : k ∈ GinfC V) : ∀ f ∈ U, rTr V k f ∈ U := by
  classical
  obtain ⟨-, -, r3, -⟩ := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hu := GlobalTheory.RealLift.archM_mem hθ V k
  have e : GlobalTheory.RealLift.prodAt θ V Finset.univ.toList (fun τ => Formalism.L2.Pj.archM V (θ τ) k) = k :=
    r3 _ (GlobalTheory.RealLift.prodAt_mem θ V _ _) _ hk fun τ => by
      rw [GlobalTheory.RealLift.infMat_prodAt hθ V hu τ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
      rfl
  rw [← e]
  clear e
  generalize (Finset.univ.toList : List D.what₂.Tau) = l
  induction l with
  | nil =>
    intro f hf
    convert hf using 1
    funext g
    exact congrArg f (mul_one g)
  | cons τ l ih =>
    intro f hf
    convert hU τ _ (hu τ) _ (ih f hf) using 1
    funext g
    exact congrArg f (mul_assoc _ _ _).symm

open Classical in
theorem actT_tprod (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    inclT M (PiTensorProduct.tprod ℂ (Function.update v τ w)) = actT M τ g (inclT M (PiTensorProduct.tprod ℂ v)) := by
  unfold inclT actT
  simp only [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases c : ρ = τ
  · subst c
    simpa using hw
  · simp [Function.update_of_ne c]

theorem mem_multT_of_equivariant : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ) (L : SmT M →ₗ[ℂ] (GA D V → ℂ)), IsInfFam θ → V.SigOK → AllPlus M → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → FiniteDimensional ℂ (SmT M) → Function.Injective (inclT M) → IsTensAct M π → (∀ x, IsAutFun V (L x)) → (∀ x, ∀ k ∈ J, ∀ g, L x (g * k) = χ k * L x g) → (∀ τ u x, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x)) → L ∈ MultT θ M J χ := by
  intro D θ V S M π J χ L hθ hs hp hfd hT hinj hπ haut hlev heq
  have hd := isDefinite hs hp
  refine (mem_multT θ M J χ L).2 (Submodule.subset_span ?_)
  have e : ∀ v : M.Vec, PiTensorProduct.lift.symm L v = L (PiTensorProduct.tprod ℂ v) := fun v => rfl
  refine ⟨fun v => ?_, fun v => GlobalTheory.DefiniteEnd.isCuspFun_of_definite hs hd _, fun v k hk g => hlev _ k hk g,
    fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · rw [e]
    refine (GlobalTheory.DefiniteForms.autFunDefIffSm D θ hθ V hs hd _).1 ⟨haut _, ?_⟩
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, hk, rfl⟩
    refine rTr_mem hθ _ (fun τ g hg => ?_) hk _ (LinearMap.mem_range_self L _)
    rintro _ ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
    exact ⟨_, heq τ u x⟩
  · obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
    rw [e, e, ← heq]
    congr 1
    exact hinj ((actT_tprod τ _ v w hw).trans (hπ τ u _).symm)
  · haveI := (hfd τ).1
    exact GlobalTheory.DefiniteEnd.exists_sobCont M τ _ v x

end GlobalTheory.DefLiftMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem interNum_one_lbPow_of_curve {κ : Type} [Field κ] {C : Scheme.{0}} [Algebra κ Γ(C, ⊤)]
    [IsProper (strHom κ (X := C))] {H N : LB C} (hH : IsAmpleLB H) (hd : topologicalKrullDim C = 1)
    (hN : N.IsLB) (n : ℕ) :
    interNum κ (structureModule C) ![lbPow N n] = n * interNum κ (structureModule C) ![N] := by
  induction n with
  | zero =>
    rw [interNum_eq_zero_of_cls_eq_zero κ _ (isLB_vecOne (isLB_lbPow hN 0)) 0
      ((cls_lbPow hN 0 _).trans (zero_nsmul _))]
    simp
  | succ n ih =>
    rw [interNum_one_of_cls_eq_add hH hd (isLB_lbPow hN (n + 1)) (isLB_lbPow hN n) hN
      (by
        calc
          _ = (n + 1) • cls N hN := cls_lbPow hN (n + 1) _
          _ = n • cls N hN + cls N hN := succ_nsmul _ _
          _ = _ := by rw [cls_lbPow hN n _]), ih]
    push_cast
    ring

theorem nefFib_pow_iff : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0})
    (p : X ⟶ Sp k), IsProjOver p → ∀ (L : HermLB p) (m : ℕ), 0 < m →
      (ArInt.NefFib (L.pow m) ↔ ArInt.NefFib L) := by
  intro k _ _ X p hp L m hm
  obtain ⟨hpr, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have key : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
      [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 →
      topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
    intro Z i _ _ κ _ _ _ hd
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
    have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    have hAZ := hA.pull_of_isClosedImmersion i
    have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
    have e1 : topSelfIntersection κ ((L.pow m).B.pull i) 1 =
        interNum κ (structureModule Z) ![lbPow (L.B.pull i) m] :=
      interNum_congr_cls κ _ (fun _ => LB.isLB_pull (L.pow m).isLB i)
        (isLB_vecOne (isLB_lbPow hN m)) fun j => by
          fin_cases j
          exact (cls_pull (L.pow m).isLB i _).trans
            ((congrArg (pull i) (cls_lbPow L.isLB m (L.pow m).isLB)).trans
              ((map_nsmul (pull i) m _).trans (cls_lbPow hN m _).symm))
    have e2 : topSelfIntersection κ (L.B.pull i) 1 = interNum κ (structureModule Z) ![L.B.pull i] := by
      rw [topSelf_def]
      congr 1
      funext j
      fin_cases j
      rfl
    rw [e1, e2]
    exact interNum_one_lbPow_of_curve hAZ hd hN m
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  constructor
  · intro h Z i _ _ κ _ _ _ hd
    have h' := h Z i κ hd
    rw [key Z i κ hd] at h'
    exact (mul_nonneg_iff_of_pos_left hm').1 h'
  · intro h Z i _ _ κ _ _ _ hd
    rw [key Z i κ hd]
    exact mul_nonneg hm'.le (h Z i κ hd)

end GlobalTheory.ArInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormInfIsometryConjLeConstMul
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem sum_norm_conj_le {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) :
    ∑ i, ∑ j, ‖(P * A * Q) i j‖ ≤
      ((m : ℝ) * m * (∑ i, ∑ k, ‖P i k‖) * (∑ l, ∑ j, ‖Q l j‖)) * ∑ k, ∑ l, ‖A k l‖ := by
  set cP := ∑ i, ∑ k, ‖P i k‖
  set cQ := ∑ l, ∑ j, ‖Q l j‖
  set S := ∑ k, ∑ l, ‖A k l‖
  have hP : ∀ i k, ‖P i k‖ ≤ cP := fun i k =>
    (Finset.single_le_sum (f := fun k => ‖P i k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun i => ∑ k, ‖P i k‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ i))
  have hQ : ∀ l j, ‖Q l j‖ ≤ cQ := fun l j =>
    (Finset.single_le_sum (f := fun j => ‖Q l j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun l => ∑ j, ‖Q l j‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ l))
  have hcP : 0 ≤ cP := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcQ : 0 ≤ cQ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hent : ∀ i j, ‖(P * A * Q) i j‖ ≤ cP * cQ * S := by
    intro i j
    have e : (P * A * Q) i j = ∑ l, ∑ k, P i k * A k l * Q l j := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [e]
    calc ‖∑ l, ∑ k, P i k * A k l * Q l j‖ ≤ ∑ l, ∑ k, ‖P i k‖ * ‖A k l‖ * ‖Q l j‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (norm_sum_le _ _).trans (le_of_eq ?_))
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_mul]
      _ ≤ ∑ l, ∑ k, cP * ‖A k l‖ * cQ := by
          refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hP i k) (norm_nonneg _)) (hQ l j) (norm_nonneg _)
            (mul_nonneg hcP (norm_nonneg _))
      _ = cP * cQ * S := by
          rw [Finset.sum_comm]
          simp only [S, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  calc ∑ i, ∑ j, ‖(P * A * Q) i j‖ ≤ ∑ _i : Fin m, ∑ _j : Fin m, cP * cQ * S :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem normInf_kap_le : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA D V, normInf θ V' (I.kap g) ≤ C * normInf θ V g := by
  intro D V V' I θ hθ
  let K : D.what₂.Tau → ℝ := fun τ =>
    (V'.rank : ℝ) * V'.rank * (∑ i, ∑ k, ‖I.pT τ i k‖) * (∑ l, ∑ j, ‖I.qT τ l j‖)
  have hK : ∀ τ, 0 ≤ K τ := fun τ => by positivity
  refine ⟨∑ τ, K τ, Finset.sum_nonneg fun τ _ => hK τ, fun g => ?_⟩
  unfold normInf
  have key : ∀ τ, (∑ i, ∑ j, (‖infMat D.sp.cm.sig V'.gram (θ τ) (I.kap g) i j‖ +
      ‖infMat D.sp.cm.sig V'.gram (θ τ) (I.kap g)⁻¹ i j‖)) ≤
      K τ * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := by
    intro τ
    rw [← map_inv I.kap g, I.infMat_kap hθ, I.infMat_kap hθ]
    simp only [Finset.sum_add_distrib, mul_add]
    exact add_le_add (sum_norm_conj_le _ _ _) (sum_norm_conj_le _ _ _)
  have hS : ∀ τ, 0 ≤ ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := fun τ => by positivity
  calc _ ≤ ∑ τ, K τ * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
          ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := Finset.sum_le_sum fun τ _ => key τ
    _ ≤ ∑ τ, (∑ σ, K σ) * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
          ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) :=
        Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun σ _ => hK σ) (Finset.mem_univ τ)) (hS τ)
    _ = _ := by rw [← Finset.mul_sum]

end GlobalTheory.Mem.Isom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSupportKerMulSectionOfNonvanishing
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.KernelCut

private theorem subsingleton_kernel_sections_of_app_injective {Y : Scheme.{0}} {M N : Y.Modules} (φ : M ⟶ N)
    (V : Y.Opens) (hφ : ∀ t, φ.app V t = 0 → t = 0) : Subsingleton Γ(kernel φ, V) := by
  have hmono : Mono ((kernel.ι φ).app V) := by
    have h1 : Mono ((Scheme.Modules.toPresheaf Y).map (kernel.ι φ)) := inferInstance
    exact (NatTrans.mono_iff_mono_app _).1 h1 (Opposite.op V)
  have hinj := (AddCommGrpCat.mono_iff_injective _).1 hmono
  have key : ∀ c : Γ(kernel φ, V), c = 0 := by
    intro c
    apply hinj
    rw [map_zero]
    apply hφ
    have h2 : (kernel.ι φ ≫ φ).app V c = 0 := by simp
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h2
    exact h2
  exact ⟨fun a b => by rw [key a, key b]⟩

private theorem notMem_support_of_subsingleton_sections {Y : Scheme.{0}} (K : Y.Modules) {x : Y} (W : Y.Opens)
    (hxW : x ∈ W) (h : ∀ V : Y.Opens, V ≤ W → Subsingleton Γ(K, V)) : x ∉ support K := by
  unfold support
  simp only [Set.mem_ofPred_eq, not_nontrivial_iff_subsingleton]
  have key : ∀ c : K.presheaf.stalk x, c = 0 := by
    intro c
    obtain ⟨U, hxU, t, rfl⟩ := K.presheaf.exists_germ_eq c
    rw [← K.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ W ≤ U)) x ⟨hxU, hxW⟩ t]
    have := h (U ⊓ W) inf_le_right
    rw [Subsingleton.elim (K.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op t) 0, map_zero]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem notMem_support_kernel_cutHom : ∀ {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (s : L.Sec) (G : Y.Modules) [G.IsQuasicoherent], ∀ x ∈ Out.nonzeroLocus s, x ∉ support (kernel (cutHom G hL s)) := by
  intro Y L hL s G _ x hx
  have hx' : x ∈ ⨆ k, Y.basicOpen (s.f k) := by
    unfold Out.nonzeroLocus at hx
    exact hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
  have hle : Y.basicOpen (s.f k) ≤ Out.nonzeroLocus s := by
    unfold Out.nonzeroLocus
    exact le_iSup (fun j => Y.basicOpen (s.f j)) k
  refine notMem_support_of_subsingleton_sections _ (Y.basicOpen (s.f k)) hk fun V hV => ?_
  have hVU : V ≤ L.U k := hV.trans (Y.basicOpen_le _)
  have hmb := isMulBy_cutHom G hL s
  obtain ⟨e, he⟩ := hmb k V hVU
  have hunit : IsUnit (resG Y hVU (s.f k)) := by
    have h3 := isUnit_resG_zfun (zofSec s) k hVU
      (by rw [nonzeroLocus_zofSec hL s]; exact hV.trans hle)
    simpa using h3
  refine subsingleton_kernel_sections_of_app_injective _ V fun t ht => ?_
  rw [he] at ht
  have h4 : e t = 0 := hunit.smul_eq_zero.1 ht
  exact e.injective (h4.trans e.map_zero.symm)

end GlobalTheory.KernelCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemilinearBasisImageIndepOfBasis
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

theorem semilinear_basis_image_indep_of_basis :
    ∀ (K : Type) [Field K] (e : K →+* ℂ) (V : Type) [AddCommGroup V] [Module K V]
      (W : Type) [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) (ι κ : Type)
      (b : Module.Basis ι K V) (b' : Module.Basis κ K V),
      (LinearIndependent ℂ (fun i => j (b i)) ∧
        Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) →
      LinearIndependent ℂ (fun i => j (b' i)) ∧
        Submodule.span ℂ (Set.range fun i => j (b' i)) = ⊤ := by
  intro K _ e V _ _ W _ _ j ι κ b b' ⟨hli, hsp⟩
  letI : Algebra K ℂ := e.toAlgebra
  letI : Module K W := Module.compHom W e
  haveI : IsScalarTower K ℂ W := ⟨fun k c w => by
    change (e k * c) • w = e k • c • w
    exact mul_smul _ _ _⟩
  let j' : V →ₗ[K] W :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun k v => j.map_smulₛₗ k v }
  let L : ℂ ⊗[K] V →ₗ[ℂ] W := j'.liftBaseChange ℂ
  have hL : ∀ v : V, L (1 ⊗ₜ[K] v) = j v := fun v => by
    simp [L, j']
  let c : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  let E : ℂ ⊗[K] V ≃ₗ[ℂ] W := (b.baseChange ℂ).equiv c (Equiv.refl ι)
  have hE : (E : ℂ ⊗[K] V →ₗ[ℂ] W) = L := by
    refine (b.baseChange ℂ).ext fun i => ?_
    rw [LinearEquiv.coe_coe]
    simp only [E, Module.Basis.equiv_apply, Equiv.refl_apply, c, Module.Basis.mk_apply]
    rw [Module.Basis.baseChange_apply, hL]
  have hb : (fun i => j (b' i)) = ⇑((b'.baseChange ℂ).map E) := by
    funext i
    rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, ← hL, ← hE, LinearEquiv.coe_coe]
  rw [hb]
  exact ⟨Module.Basis.linearIndependent _, Module.Basis.span_eq _⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsInnerProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem inner_l2_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a : H →ₗ[ℂ] (X → ℂ)) (A : H →ₗ[ℂ] Lp ℂ 2 ν), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), (A w : X → ℂ) =ᵐ[ν] a w) → ∀ φ, IsTest φ → ∀ w ∈ smSub G (trRep σ P), ∀ f : Lp ℂ 2 ν, ⟪f, A (gard ε σ φ w)⟫_ℂ = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪f, A (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
  intro n ε H _ _ _ σ P G hP hG hσ X _ _ _ _ ν _ act hact a A ha hsob hA φ hφ w hw f
  have hemb := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Formalism.REAL.UJ ε) := hemb.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Formalism.REAL.UJ ε) := hemb.locallyCompactSpace
  haveI : SigmaFinite (Formalism.REAL.muG ε) := inferInstance
  obtain ⟨hc, ⟨C, hC⟩, hact'⟩ := ha w hw
  have key : ∀ v ∈ smSub G (trRep σ P), ⟪f, A v⟫_ℂ = ∫ x, ⟪f x, a v x⟫_ℂ ∂ν := fun v hv => by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hA v hv] with x hx
    rw [hx]
  have h1 : ∀ x, a (gard ε σ φ w) x = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • a w (act g x) ∂(Formalism.REAL.muG ε) := fun x => by
    have := ((_root_.GlobalTheory.SobGarding.sobCont_gard n ε H σ P G hP hG hσ _ (hsob x)).2 w hw).2 φ hφ
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, hact'] at this
    exact this
  have hφi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) (Formalism.REAL.muG ε) := by
    simpa using hφ.integrable (ε := ε) (F := fun _ => (1 : ℝ)) continuous_const
  have hf1 : Integrable (f : X → ℂ) ν := (Lp.memLp f).integrable (by norm_num)
  have hint : Integrable (fun p : Formalism.REAL.UJ ε × X => φ (umat p.1) • ⟪f p.2, a w (act p.1 p.2)⟫_ℂ)
      ((Formalism.REAL.muG ε).prod ν) := by
    refine Integrable.mono' ((hφi.norm.mul_prod hf1.norm).mul_const C) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine AEStronglyMeasurable.smul hφi.aestronglyMeasurable.comp_fst ?_
      exact AEStronglyMeasurable.inner hf1.aestronglyMeasurable.comp_snd (hc.comp hact).aestronglyMeasurable
    · rw [norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))) (norm_nonneg _)
  rw [key _ (gard_mem hP hG hσ hφ w)]
  calc ∫ x, ⟪f x, a (gard ε σ φ w) x⟫_ℂ ∂ν
      = ∫ x, ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪f x, a w (act g x)⟫_ℂ ∂(Formalism.REAL.muG ε) ∂ν := by
        congr 1
        funext x
        have hcx : Continuous fun g : Formalism.REAL.UJ ε => a w (act g x) :=
          hc.comp (hact.comp (Continuous.prodMk_left x))
        rw [h1, ← integral_inner (hφ.integrable hcx)]
        congr 1
        funext g
        rw [← Complex.coe_smul, inner_smul_right, Complex.real_smul]
    _ = ∫ g : Formalism.REAL.UJ ε, ∫ x, φ (umat g) • ⟪f x, a w (act g x)⟫_ℂ ∂ν ∂(Formalism.REAL.muG ε) :=
        (integral_integral_swap (f := fun (g : Formalism.REAL.UJ ε) (x : X) => φ (umat g) • ⟪f x, a w (act g x)⟫_ℂ) hint).symm
    _ = _ := by
        congr 1
        funext g
        rw [integral_smul, key _ (sigma_mem hP hG hσ hw g.2)]
        simp only [hact']

end GlobalTheory.SmVec
end

