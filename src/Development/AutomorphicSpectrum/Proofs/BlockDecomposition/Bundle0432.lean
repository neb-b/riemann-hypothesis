module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0329
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUnique
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveRestrictionOfBdsqVanish
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOpenCellRetraction
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Proj

section Alg

variable (k : Type) [Field k]

def rGL {a b : ℕ} (h : a = b) : GL (Fin a) k ≃* GL (Fin b) k := h ▸ MulEquiv.refl _

theorem rGL_apply {a b : ℕ} (h : a = b) (g : GL (Fin a) k) (r c : Fin b) :
    ((rGL k h g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k) r c =
      (g : Matrix (Fin a) (Fin a) k) (Fin.cast h.symm r) (Fin.cast h.symm c) := by
  subst h
  rfl

theorem rGL_rGL {a b : ℕ} (h : a = b) (h' : b = a) (g : GL (Fin a) k) : rGL k h' (rGL k h g) = g := by
  subst h
  rfl

theorem continuous_rGL [TopologicalSpace k] {a b : ℕ} (h : a = b) : Continuous (rGL k h) := by
  subst h
  exact continuous_id

theorem castM_val {a b : ℕ} (h : a = b) (h' : a + 1 = b + 1) (M : Mir k a) :
    ((castM k h M : Mir k b) : GL (Fin (b + 1)) k) = rGL k h' (M : GL (Fin (a + 1)) k) := by
  subst h
  rfl

theorem mirProj_eq_one_of_unip (n : ℕ) (u : Mir k n) (v : Multiplicative (Fin n → k))
    (hu : (u : GL (Fin (n + 1)) k) = unip k n v) : mirabolicProjection k n u = 1 := by
  ext i j
  show blockMat k n ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j = _
  rw [hu]
  simp [blockMat, unip, colMat, Fin.castSucc_ne_last, one_apply]
  change (if i.castSucc = j.castSucc then (1 : k) else 0) = if i = j then 1 else 0
  simp

theorem ePG_true_val (i t : ℕ) (b : Fin t) : ((ePG i t ⟨true, b⟩ : Fin (i + t + 1)) : ℕ) = i + b := by
  simp [ePG]

theorem ePG_false_castSucc_val (i t : ℕ) (a : Fin i) :
    ((ePG i t ⟨false, Fin.castSucc a⟩ : Fin (i + t + 1)) : ℕ) = a := by
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem wGL_conj_apply (i t : ℕ) (A : GL (Fin ((i + 1) + t + 1)) k) (r c : Fin ((i + 1) + t + 1)) :
    (((wGL k i t)⁻¹ * A * wGL k i t : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) r c =
      (A : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (piPerm i t r) (piPerm i t c) := by
  have e1 : (((wGL k i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) = Equiv.Perm.permMatrix k (piPerm i t) := rfl
  have e2 : ((wGL k i t : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) = Equiv.Perm.permMatrix k (piPerm i t)⁻¹ := rfl
  rw [Units.val_mul, Units.val_mul, e1, e2, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Matrix.submatrix_apply, Equiv.Perm.inv_def]

theorem piPerm_cast (i t : ℕ) (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) (h : i + (t + 1) + 1 = (i + 1) + t + 1) :
    piPerm i t (Fin.cast h (ePG i (t + 1) s)) = eGP (i + 1) t s := by
  simp [piPerm]

theorem proj_eq (i t : ℕ) (h : Mir k ((i + 1) + t + 1)) (d : Fin (t + 1) → k) (M : Mir k ((i + 1) + t))
    (x : Mir k ((i + 1) + t + 1))
    (e : dEmb k i t d * wEl k i t * sEmb k _ M = h * wEl k i t * x) :
    (M : GL (Fin ((i + 1) + t + 1)) k) =
      ((wGL k i t)⁻¹ * mirabolicProjection k _ h * wGL k i t) * mirabolicProjection k _ x := by
  have e1 := congrArg (mirabolicProjection k ((i + 1) + t + 1)) e
  rw [map_mul, map_mul, map_mul, map_mul] at e1
  have h1 : mirabolicProjection k ((i + 1) + t + 1) (dEmb k i t d) = 1 := mirProj_eq_one_of_unip k _ _ _ rfl
  have h2 : mirabolicProjection k ((i + 1) + t + 1) (wEl k i t) = wGL k i t := GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi k _ _
  have h3 : mirabolicProjection k ((i + 1) + t + 1) (sEmb k _ M) = (M : GL (Fin ((i + 1) + t + 1)) k) :=
    GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi k _ _
  rw [h1, h2, h3, one_mul] at e1
  rw [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, e1, mul_assoc]

end Alg

theorem exists_parab_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), ∃ Θ : Mir k ((i + 1) + t + 1) → GL (Fin (i + (t + 1) + 1)) k, Continuous Θ ∧ Θ 1 = 1 ∧
    ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) → ∀ (d : Fin (t + 1) → k) (m : Mir k (i + (t + 1)))
      (x : Mir k ((i + 1) + t + 1)), dEmb k i t d * wEl k i t * sO k i t m = h * wEl k i t * x →
      ∃ p ∈ parab k (ePG i (t + 1)), (m : GL (Fin (i + (t + 1) + 1)) k) = p * Θ x := by
  intro k _ _ _ _ i t
  have hn : (i + 1) + t + 1 = i + (t + 1) + 1 := by omega
  refine ⟨fun x => rGL k hn (mirabolicProjection k _ x),
    (continuous_rGL k hn).comp (GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k _), by simp, ?_⟩
  intro h hh d m x e
  have e2 := proj_eq k i t h d (castM k (by omega) m) x e
  rw [castM_val k _ hn.symm] at e2
  refine ⟨rGL k hn ((wGL k i t)⁻¹ * mirabolicProjection k _ h * wGL k i t), ?_, ?_⟩
  · rw [mem_parab_iff]
    intro a b u v hab
    cases a <;> cases b <;> first | exact absurd hab (by decide) | skip
    rw [rGL_apply, wGL_conj_apply, piPerm_cast, piPerm_cast]
    have hh' : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1)) := hh
    have h0 := mem_parab_iff.1 hh' true false u (Fin.castSucc v) (by decide)
    have e3 : Fin.castSucc (eGP (i + 1) t ⟨true, u⟩) = ePG (i + 1) (t + 1) ⟨true, u⟩ :=
      Fin.ext (by rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val, ePG_true_val])
    have e4 : Fin.castSucc (eGP (i + 1) t ⟨false, v⟩) = ePG (i + 1) (t + 1) ⟨false, Fin.castSucc v⟩ :=
      Fin.ext (by rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val, ePG_false_castSucc_val])
    show ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val
      (Fin.castSucc (eGP (i + 1) t ⟨true, u⟩)) (Fin.castSucc (eGP (i + 1) t ⟨false, v⟩)) = 0
    rw [e3, e4]
    exact h0
  · have e5 := congrArg (rGL k hn) e2
    rw [rGL_rGL, map_mul] at e5
    exact e5

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Proj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSInf
section
noncomputable section

open NumberField IsDedekindDomain Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.JSInfStep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem nonempty_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩⟩

variable [_root_.NumberField.IsTotallyComplex E]

def chiInf (ψ : AddChar (Ad E) ℂ) : AddChar (Cinf E) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHomClass.toAddMonoidHom (sInf E))

theorem chiInf_apply (ψ : AddChar (Ad E) ℂ) (z : Cinf E) : chiInf ψ z = ψ (sInf E z) := rfl

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

theorem pInf_sInf (x : Cinf E) : pInf E (sInf E x) = x := (infEq E).symm_apply_apply x

theorem pFin_sInf (x : Cinf E) : pFin E (sInf E x) = 0 := rfl

theorem chiInf_nondeg {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (z : Cinf E)
    (h : ∀ w, chiInf ψ (z * w) = 1) : z = 0 := by
  obtain ⟨d, hd⟩ := hψ.ann (sInf E z) fun c => by
    have e : sInf E z * algebraMap E (Ad E) c = sInf E (z * pInf E (algebraMap E (Ad E) c)) := by
      refine ad_ext ?_ ?_
      · rw [map_mul, pInf_sInf, pInf_sInf]
      · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]
    rw [e]
    exact h _
  obtain ⟨w⟩ := nonempty_pl (E := E)
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  have h0 : ((pFin E).comp (algebraMap E (Ad E))) d = 0 := by
    change pFin E (algebraMap E (Ad E) d) = 0
    rw [← hd, pFin_sInf]
  have hd0 : d = 0 := (injective_iff_map_eq_zero _).1 ((pFin E).comp (algebraMap E (Ad E))).injective d h0
  rw [← pInf_sInf z, hd, hd0, map_zero, map_zero]

end GlobalTheory.CompanionTheory.JSInfStep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetFunctionJacquetKernel
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

theorem cosetFn_zero_val (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) :
    cosetFn t hc a (0 : Z) = 0 := by
  apply Subtype.ext
  funext v
  show (cosetSet t c a).indicator (fun _ => (0 : Z)) v = 0
  exact congrFun (Set.indicator_zero Z (cosetSet t c a)) v

theorem cosetFn_add_val (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) (z w : Z) :
    cosetFn t hc a (z + w) = cosetFn t hc a z + cosetFn t hc a w := by
  apply Subtype.ext
  funext v
  classical
  show (cosetSet t c a).indicator (fun _ => z + w) v =
    (cosetSet t c a).indicator (fun _ => z) v + (cosetSet t c a).indicator (fun _ => w) v
  by_cases hv : v ∈ cosetSet t c a
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, add_zero]

theorem cosetFn_smul_val (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) (r : ℂ) (z : Z) :
    cosetFn t hc a (r • z) = r • cosetFn t hc a z := by
  apply Subtype.ext
  funext v
  classical
  show (cosetSet t c a).indicator (fun _ => r • z) v =
    r • (cosetSet t c a).indicator (fun _ => z) v
  by_cases hv : v ∈ cosetSet t c a
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, smul_zero]

def topCol (i t : ℕ) (x : Fin i → k) : Multiplicative (Fin (i + t) → k) :=
  Multiplicative.ofAdd (topV k i t x)

theorem topPart_topCol (i t : ℕ) (x : Fin i → k) : topP i t (topCol i t x).toAdd = x := by
  funext j
  exact Fin.append_left _ _ j

theorem middlePart_topColumn (i t : ℕ) (x : Fin i → k) : middlePart i t (topCol i t x).toAdd = 0 := by
  funext j
  exact Fin.append_right _ _ j

theorem fibAct_topCol {i : ℕ} (t : ℕ) (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z)
    {c : k} (hc : c ≠ 0) (x : Multiplicative (Fin i → k)) (w : Z) :
    fibAct t ρ₀ (topCol i t x.toAdd) (cosetFn t hc 0 w) = cosetFn t hc 0 (ρ₀ x w) := by
  apply Subtype.ext
  funext v
  classical
  have h1 : (fibAct t ρ₀ (topCol i t x.toAdd) (cosetFn t hc 0 w)).1 v =
      ρ₀ (Multiplicative.ofAdd (topP i t (topCol i t x.toAdd).toAdd))
        ((cosetFn t hc 0 w).1 (v + middlePart i t (topCol i t x.toAdd).toAdd)) :=
    fibAct_apply t ρ₀ _ _ v
  have h2 : Multiplicative.ofAdd (topP i t (topCol (k := k) i t x.toAdd).toAdd) = x := by
    rw [topPart_topCol]
    rfl
  rw [h1, h2, middlePart_topColumn, add_zero]
  show ρ₀ x ((cosetSet t c 0).indicator (fun _ => w) v) =
    (cosetSet t c 0).indicator (fun _ => ρ₀ x w) v
  by_cases hv : v ∈ cosetSet t c 0
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, map_zero]

theorem cosetFn_mem_twKer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (z : Z)
    (hz : z ∈ twKer ρ₀ ⊤ 1) : cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, v, rfl⟩ := hw
    refine Submodule.subset_span ⟨⟨topCol i t (n : Multiplicative (Fin i → k)).toAdd, trivial⟩,
      cosetFn t hc 0 v, ?_⟩
    have hsub : ρ₀ (n : Multiplicative (Fin i → k)) v - ((1 : (⊤ : Subgroup (Multiplicative (Fin i → k))) →* ℂˣ) n : ℂ) • v =
        ρ₀ (n : Multiplicative (Fin i → k)) v + (-1 : ℂ) • v := by
      simp [sub_eq_add_neg]
    have hrhs : fibAct t ρ₀ (topCol i t (n : Multiplicative (Fin i → k)).toAdd) (cosetFn t hc 0 v) -
        ((1 : (⊤ : Subgroup (Multiplicative (Fin (i + t) → k))) →* ℂˣ) ⟨topCol i t (n : Multiplicative (Fin i → k)).toAdd, trivial⟩ : ℂ) • cosetFn t hc 0 v =
        cosetFn t hc 0 (ρ₀ (n : Multiplicative (Fin i → k)) v) + (-1 : ℂ) • cosetFn t hc 0 v := by
      rw [fibAct_topCol]
      simp [sub_eq_add_neg]
    rw [hsub, cosetFn_add_val, cosetFn_smul_val]
    exact hrhs.symm
  | zero => rw [cosetFn_zero_val]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [cosetFn_add_val]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [cosetFn_smul_val]; exact Submodule.smul_mem _ r ha

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConstantTermSmall
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem norm_le_of_unipRad_variation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) → Continuous φ → IsCuspidal σ J φ → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), 0 < k → GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ (g : GAd σ J) (e : ℝ), (∀ m ∈ unipRad σ J Cc, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  intro F E _ _ _ _ _ σ hCM n J hJ φ hleft hcont hcusp k Cc hk hC g e he
  haveI := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC
  have hc : GlobalTheory.Cusp.Cocompact (ratPts σ J) (unipRad σ J Cc) := GlobalTheory.UAut.cocompact_unipRad hCM hJ hC
  haveI hP := hc.isProbabilityMeasure
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) φ := hleft
  have h0 : GlobalTheory.Cusp.constTermOn (ratPts σ J) (unipRad σ J Cc) φ g = 0 :=
    (hc.constTermOn_eq_zero_iff (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ Measure.haar) hL g).2
      (hcusp k Cc ⟨hk, hC.1, hC.2⟩ _ _ inferInstance (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ _) g)
  have hI := hc.integrable hL hcont g
  have key : φ g = ∫ q, (φ g - φ ((q.out : unipRad σ J Cc) * g))
      ∂GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc) := by
    rw [integral_sub (integrable_const _) hI]
    have h0' : ∫ q, φ ((q.out : unipRad σ J Cc) * g)
        ∂GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc) = 0 := h0
    rw [h0', integral_const]
    simp
  rw [key]
  have hb := norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc))
    (f := fun q => φ g - φ ((q.out : unipRad σ J Cc) * g)) (C := e)
    (.of_forall fun q => by rw [norm_sub_rev]; exact he _ (q.out : unipRad σ J Cc).2)
  simpa using hb

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalGeneralizedSpaceSpanClosed
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspSubspace

theorem mem_of_mem_span_cuspForms :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
      (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W)
      (J : Set (Module.End ℂ (Sm E a))),
      ∀ φ ∈ Submodule.span ℂ {φ : Sm E a | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1},
        φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 := by
  intro E _ _ _ a L W _ _ ρ J φ hφ
  induction hφ using Submodule.span_induction with
  | mem x h => exact h
  | zero =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).zero_mem, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    change ∫ _ in 𝓕, (0 : ℂ) ∂μ = 0
    simp
  | add x y _ _ hx hy =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).add_mem hx.1 hy.1, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have ix := (GlobalTheory.CompanionTheory.ConstTerm.integrableOn_fundamentalDomain E a r x hx.1.1.left hx.1.1.level μ 𝓕 hμ hF).2 g
    have iy := (GlobalTheory.CompanionTheory.ConstTerm.integrableOn_fundamentalDomain E a r y hy.1.1.left hy.1.1.level μ 𝓕 hμ hF).2 g
    have e : ∫ u in 𝓕, (x + y).1 (unip u * g) ∂μ =
        (∫ u in 𝓕, x.1 (unip u * g) ∂μ) + ∫ u in 𝓕, y.1 (unip u * g) ∂μ := integral_add ix iy
    rw [e, hx.2 r hr hr' μ 𝓕 hμ hF g, hy.2 r hr hr' μ 𝓕 hμ hF g, add_zero]
  | smul c x _ hx =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).smul_mem c hx.1, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have e : ∫ u in 𝓕, (c • x).1 (unip u * g) ∂μ = c • ∫ u in 𝓕, x.1 (unip u * g) ∂μ :=
      integral_smul c _
    rw [e, hx.2 r hr hr' μ 𝓕 hμ hF g, smul_zero]

end GlobalTheory.CompanionTheory.CuspSubspace

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupFrobeniusFactor
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.TameDecomp

theorem exists_frob_pow_mul_pow_mul_inertia : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ g : Dec (F := F) A, ∃ a < N, ∃ t i : Dec (F := F) A, (i : G F Ω) ∈ Ine (F := F) A ∧ g = φ ^ a * t ^ N * i := by
  intro F Ω _ _ _ _ _ A v hA φ hφ N hN g
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  set I : Subgroup (Dec (F := F) A) := (Ine (F := F) A).subgroupOf (Dec (F := F) A) with hI
  have hIc : IsClosed (I : Set (Dec (F := F) A)) := (isClosed_Ine A).preimage continuous_subtype_val
  let P : Set (Dec (F := F) A) :=
    (fun x : Dec (F := F) A × Dec (F := F) A => x.1 ^ N * x.2) '' (Set.univ ×ˢ (I : Set _))
  have hP : IsCompact P := (isCompact_univ.prod hIc.isCompact).image (by fun_prop)
  let Wd : Set (Dec (F := F) A) := ⋃ a ∈ Finset.range N, (fun x => φ ^ a * x) '' P
  have hW : IsClosed Wd := by
    refine (Finset.isCompact_biUnion _ fun a _ => hP.image (by fun_prop)).isClosed
  have hsub : ((Subgroup.zpowers φ ⊔ I : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) ⊆ Wd := by
    intro x hx
    rw [Subgroup.mul_normal] at hx
    obtain ⟨h, hh, i, hi, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hN' : (0 : ℤ) < N := by exact_mod_cast hN
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg m hN'.ne')
    have haN : a < N := by
      have := Int.emod_lt_of_pos m hN'
      omega
    have e : φ ^ m = φ ^ a * (φ ^ (m / (N : ℤ))) ^ N := by
      rw [← zpow_natCast (φ ^ (m / (N : ℤ))) N, ← zpow_mul, ← zpow_natCast φ a, ← zpow_add]
      congr 1
      have := Int.emod_add_mul_ediv m N
      rw [ha] at this
      rw [mul_comm (m / (N : ℤ))]
      omega
    refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 haN)) ?_
    exact ⟨_, ⟨(φ ^ (m / (N : ℤ)), i), ⟨Set.mem_univ _, hi⟩, rfl⟩, by
      simp only [e, mul_assoc]⟩
  have hg : g ∈ Wd := by
    have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA φ hφ
    have h2 : g ∈ (Subgroup.zpowers φ ⊔ I).topologicalClosure := by rw [hI, h1]; trivial
    exact closure_minimal hsub hW h2
  simp only [Wd, Set.mem_iUnion] at hg
  obtain ⟨a, ha, y, ⟨⟨t, i⟩, ⟨-, hi⟩, rfl⟩, e⟩ := hg
  exact ⟨a, Finset.mem_range.1 ha, t, i, Subgroup.mem_subgroupOf.1 hi, by
    rw [← e, mul_assoc]⟩

end GlobalTheory.CompanionTheory.TameDecomp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantHeckeOperatorsCommute
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.CassHecke

theorem isHeckeOpG_mul_mem {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} {K : Subgroup G} {g c : G} (hc : c ∈ K)
    {T : Module.End ℂ (fixed π K)} (h : PositivityTheory.Lbc.IsHeckeOpG π K g T) :
    PositivityTheory.Lbc.IsHeckeOpG π K (g * c) T := by
  intro v f hf
  have hv : π c (v : V) = v := by simpa using v.2 ⟨c, hc⟩
  rw [map_mul, Module.End.mul_apply, hv]
  exact h v f hf

theorem heckeOp_commute : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), (∀ a ∈ D.T, ∀ b ∈ D.T, a * b * a⁻¹ * b⁻¹ ∈ D.J) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
    ∀ t t' : D.T, D.IsDom t → D.IsDom t' → ∀ U U' : Module.End ℂ (fixed π D.J),
    PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → PositivityTheory.Lbc.IsHeckeOpG π D.J (t' : G) U' → U * U' = U' * U := by
  intro G _ _ _ D hcomm V _ _ π hπ t t' ht ht' U U' hU hU'
  have h1 := _root_.GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract G D V π hπ t t' ht ht' U U' hU hU'
  have h2 := _root_.GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract G D V π hπ t' t ht' ht U' U hU' hU
  have hc : (t' : G)⁻¹ * (t : G)⁻¹ * (t' : G) * (t : G) ∈ D.J := by
    have := hcomm (t' : G)⁻¹ (D.T.inv_mem t'.2) (t : G)⁻¹ (D.T.inv_mem t.2)
    simpa using this
  have h3 : PositivityTheory.Lbc.IsHeckeOpG π D.J ((t : G) * t') (U' * U) := by
    have := isHeckeOpG_mul_mem (D.J.inv_mem hc) h2
    have e : (t' : G) * (t : G) * ((t' : G)⁻¹ * (t : G)⁻¹ * (t' : G) * (t : G))⁻¹ = (t : G) * t' := by
      group
    rwa [e] at this
  exact (_root_.GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique G D.J D.isOpen_J D.isCompact_J V π hπ ((t : G) * t')).unique h1 h3

end GlobalTheory.CompanionTheory.CassHecke
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNontrivialDerivativeStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nontrivial_derivative : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k m) V), IsSmooth τ → Nontrivial V → ∃ n ≤ m, Nontrivial (TwJacquet τ (derUnipM k m n) (derCharM k ψ m n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial | exact GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial | (intros; apply GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveRestrictionOfBdsqVanishStatement
section
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_restriction_of_bdsq_vanish : PositivityTheory.RgBcC.RealD.BdSqL → PositivityTheory.RgBcC.RealD.VanKL → PositivityTheory.RgBcC.RealD.InjRL := by
  first | exact @GlobalTheory.CompanionTheory.InjRL.injRL_of | exact GlobalTheory.CompanionTheory.InjRL.injRL_of | (intros; apply GlobalTheory.CompanionTheory.InjRL.injRL_of <;> assumption)
end

