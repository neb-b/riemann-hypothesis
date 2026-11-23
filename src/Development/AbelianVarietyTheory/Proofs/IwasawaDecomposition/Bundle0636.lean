module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLineIffEigenSpan
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanTie

section Core

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 4000000 in
theorem mem_goodL_iff_iotaR (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hU : R.toRealDat.LUnif) (hW : R.toRealDat.models_HW)
    (hidem : ∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g))
    (hψ : LvlPsi R F cG θ) (j : ℕ) (v : (ratDatR R cG kKs hk).WL j) :
    v ∈ goodL D (ratDatR R cG kKs hk) θ j ↔
      GlobalTheory.EigSpanDesc.iotaR R (idxOf D j) v ∈ GlobalTheory.EigRows.goodW R.toRealDat F.lv2 (idxOf D j) := by
  have hinj : Function.Injective fun x : Fin (R.nW (idxOf D j)) → D.what₂.LL =>
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x) := by
    refine (hW _ _).1.comp ((injective_iff_map_eq_zero ((R.FW (idxOf D j)).j (sg0 D A3.A))).2 fun x hx => ?_)
    by_contra hne
    exact ((hU _ _).1 1 (fun _ => x) (linearIndependent_unique_iff.2 hne)).ne_zero 0 hx
  have hact : ∀ (g : G) (x : Fin (R.nW (idxOf D j)) → D.what₂.LL),
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A)
        ((((R.FW (idxOf D j)).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW (idxOf D j)).ρ g x)) =
      postOn _ (Links.actL (Wc D (idxOf D j)) (R.βW (idxOf D j)) (R.datWp (idxOf D j) R.triv) (R.eG g))
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x)) := fun g x => by
    rw [map_smulₛₗ, map_smul, (hU _ _).2.2, smul_smul, ← map_mul, inv_mul_cancel₀ (Units.ne_zero _), map_one, one_smul]
  have hactL : ∀ (g : G) (x : (ratDatR R cG kKs hk).WL j),
      GlobalTheory.HeightCounting.actL D (ratDatR R cG kKs hk) j ((R.eG.trans cG) g) x =
        (((R.FW (idxOf D j)).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW (idxOf D j)).ρ g x := fun g x => by
    show ((((R.FW (idxOf D j)).chi ((R.eG.trans cG).symm ((R.eG.trans cG) g)) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ •
      (R.FW (idxOf D j)).ρ ((R.eG.trans cG).symm ((R.eG.trans cG) g)) x = _
    rw [MulEquiv.symm_apply_apply]
  have hsum : ∀ x : (ratDatR R cG kKs hk).WL j,
      (∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • GlobalTheory.HeightCounting.actL D (ratDatR R cG kKs hk) j g) x =
        ∑ g : G, (idemOf A3.A.X).coeff g •
          ((((R.FW (idxOf D j)).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW (idxOf D j)).ρ g x) := fun x => by
    rw [← finsum_comp_equiv (R.eG.trans cG).toEquiv, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hc : ((D.nexp.eLL0 ((R.eG.trans cG) g) : ↥D.LL0) : D.what₂.LL) = (idemOf A3.A.X).coeff g :=
      D.what₂.embLL.injective ((D.nStage_trivialCharacter_coeff_eq _).trans (hidem g).symm)
    rw [LinearMap.smul_apply, ← hactL g x, ← hc]
    rfl
  have hsmul : ∀ (c : D.what₂.LL) (x : Fin (R.nW (idxOf D j)) → D.what₂.LL),
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (c • x)) =
        sg0 D A3.A c • (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x) := fun c x => by
    rw [map_smulₛₗ, map_smul]
  have hact2 : ∀ (g : G) (x : (ratDatR R cG kKs hk).WL j),
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A)
        (GlobalTheory.HeightCounting.actL D (ratDatR R cG kKs hk) j ((R.eG.trans cG) g) x)) =
      postOn _ (Links.actL (Wc D (idxOf D j)) (R.βW (idxOf D j)) (R.datWp (idxOf D j) R.triv) (R.eG g))
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x)) := fun g x =>
    (congrArg (fun y : Fin (R.nW (idxOf D j)) → D.what₂.LL =>
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) y)) (hactL g x)).trans (hact g x)
  have hchain : (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A)
      (∑ g : G, (idemOf A3.A.X).coeff g •
        ((((R.FW (idxOf D j)).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW (idxOf D j)).ρ g v))) =
      ∑ g : G, sg0 D A3.A ((idemOf A3.A.X).coeff g) •
        postOn _ (Links.actL (Wc D (idxOf D j)) (R.βW (idxOf D j)) (R.datWp (idxOf D j) R.triv) (R.eG g))
          ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) v)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smulₛₗ, map_smul]
    exact congrArg _ (hact g v)
  rw [goodL, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, one_smul]
  change _ ↔ (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) v) ∈
    R.toRealDat.Wat (idxOf D j) (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))
  rw [GlobalTheory.LevelForms.mem_wat_iff R.toRealDat F.lv2 hU hW false]
  refine and_comm.trans (and_congr ?_ ?_)
  · constructor
    · intro h p
      have hu : (R.eG.trans cG) (p : G) ∈ Formalism.IndefR.NX.U D.nd := (hψ.1 p).1 p.2
      have h1 : GlobalTheory.HeightCounting.actL D (ratDatR R cG kKs hk) j ((R.eG.trans cG) (p : G)) v =
          (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) • v :=
        Module.End.mem_eigenspace_iff.1 (h ⟨_, hu⟩)
      rw [hψ.2 ⟨p.1, p.2⟩ hu] at h1
      exact (hact2 p v).symm.trans ((congrArg (fun y : Fin (R.nW (idxOf D j)) → D.what₂.LL =>
        (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) y)) h1).trans (hsmul _ v))
    · intro h u
      obtain ⟨u, hu⟩ := u
      obtain ⟨g, rfl⟩ := (R.eG.trans cG).surjective u
      have hg : g ∈ F.P0 := (hψ.1 g).2 hu
      have hp := hψ.2 ⟨g, hg⟩ hu
      refine Module.End.mem_eigenspace_iff.2 (hinj ?_)
      refine (hact2 g v).trans ((h ⟨g, hg⟩).trans ?_)
      rw [hp]
      exact (hsmul _ v).symm
  · rw [hsum]
    exact ⟨fun h => hchain.symm.trans (congrArg (fun y : Fin (R.nW (idxOf D j)) → D.what₂.LL =>
        (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) y)) h),
      fun h => hinj (hchain.trans h)⟩

end Core


end GlobalTheory.EigSpanTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPolyhedralCoverBalancedFormsCMField
section
noncomputable section

open Matrix NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

section Cover

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

theorem hasRedCover_of_fintype (bar : O → O) {ι : Type} [Fintype ι] (f : ι → LinearMap.BilinForm ℤ X)
    (h1 : ∀ i y z, f i y z = f i z y) (h2 : ∀ i y, 0 ≤ f i y y)
    (h : ∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (c : ι → ℝ), (∀ i, 0 ≤ c i) ∧
      pullR e.toLinearMap B = ∑ i, c i • toReal (f i)) : HasRedCover bar X := by
  let q := Fintype.equivFin ι
  refine ⟨1, fun _ => Fintype.card ι, fun _ i => f (q.symm i), fun _ i => h1 _, fun _ i => h2 _, fun B hB => ?_⟩
  obtain ⟨e, c, hc, he⟩ := h B hB
  refine ⟨e, 0, fun i => c (q.symm i), fun i => hc _, ?_⟩
  rw [he]
  exact (q.symm.sum_comp fun i => c i • toReal (f i)).symm

def sqForm {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (l : Fin n → ℤ) : LinearMap.BilinForm ℤ X :=
  let φ : X →ₗ[ℤ] ℤ := ∑ i, l i • b.coord i
  (LinearMap.mul ℤ ℤ).compl₁₂ φ φ

theorem sqForm_apply {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (l : Fin n → ℤ) (y z : X) :
    sqForm b l y z = (∑ i, l i * b.repr y i) * ∑ i, l i * b.repr z i := by
  simp [sqForm, LinearMap.sum_apply]
  rw [Finset.sum_mul_sum, Finset.sum_comm]

theorem sqForm_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (l : Fin n → ℤ) (i j : Fin n) :
    sqForm b l (b i) (b j) = l i * l j := by
  simp [sqForm_apply, Finsupp.single_apply]

theorem exists_equiv_of_actMat_eq {n : ℕ} (b b' : Module.Basis (Fin n) ℤ X)
    (h : (actMat b : O →+* _) = actMat b') : ∃ e : X ≃ₗ[O] X, ∀ i, e (b i) = b' i := by
  let g : X ≃ₗ[ℤ] X := b.equiv b' (Equiv.refl _)
  have hg : ∀ i, g (b i) = b' i := fun i => by simp [g]
  have key : ∀ (c : O) (x : X), g (c • x) = c • g x := by
    intro c x
    have h1 : (g.toLinearMap ∘ₗ (Module.toModuleEnd ℤ X c)) = (Module.toModuleEnd ℤ X c) ∘ₗ g.toLinearMap := by
      refine b.ext fun j => ?_
      change g (c • b j) = c • g (b j)
      rw [hg]
      calc g (c • b j) = g (∑ i, b.repr (c • b j) i • b i) := by rw [b.sum_repr]
        _ = ∑ i, b.repr (c • b j) i • b' i := by simp only [map_sum, map_smul, hg]
        _ = ∑ i, b'.repr (c • b' j) i • b' i := Finset.sum_congr rfl fun i _ => by
            have := congrFun (congrFun (congrArg (fun ρ : O →+* Matrix (Fin n) (Fin n) ℤ => ρ c) h) i) j
            simp only [actMat_apply] at this
            rw [this]
        _ = c • b' j := b'.sum_repr _
    exact LinearMap.congr_fun h1 x
  exact ⟨(g.toAddEquiv).toLinearEquiv key, hg⟩

theorem actMat_balanced {bar : O → O} {n : ℕ} (b : Module.Basis (Fin n) ℤ X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ}
    (hB : B ∈ realForms bar X) {G : Matrix (Fin n) (Fin n) ℝ} (hG : ∀ i j, B (b i) (b j) = G i j) (c : O) :
    ((actMat b c).map (Int.cast : ℤ → ℝ))ᵀ * G = G * (actMat b (bar c)).map (Int.cast : ℤ → ℝ) := by
  ext i j
  have e1 : B (c • b i) (b j) = ∑ k, (b.repr (c • b i) k : ℝ) * G k j :=
    calc B (c • b i) (b j) = B (∑ k, b.repr (c • b i) k • b k) (b j) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hG, zsmul_eq_mul]
  have e2 : B (b i) (bar c • b j) = ∑ k, G i k * (b.repr (bar c • b j) k : ℝ) :=
    calc B (b i) (bar c • b j) = B (b i) (∑ k, b.repr (bar c • b j) k • b k) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, hG, zsmul_eq_mul, mul_comm]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, actMat_apply]
  rw [← e1, ← e2]
  exact hB.2 c _ _

end Cover

theorem hasRedCover (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] : HasRedCover H.bar X := by
  classical
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  haveI : Module.Projective ℤ X := by
    obtain ⟨i, hi⟩ := Module.projective_def'.1 (inferInstance : Module.Projective (𝓞 E) X)
    exact Module.Projective.of_split (i.restrictScalars ℤ) ((Finsupp.linearCombination (𝓞 E) id).restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hi x)
  haveI : Module.Free ℤ X := inferInstance
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℤ X = n := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀, hB₀'⟩ := _root_.GlobalTheory.DefForm.exists_posDef_realForm E H X
  have hF := _root_.GlobalTheory.RedTh.finite_balanced_actions E H n
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.SiegelCone.gram_mem_cone n
  haveI : Nonempty (Module.Basis (Fin n) ℤ X) := ⟨Module.finBasisOfFinrankEq ℤ X hn⟩
  let ref : (𝓞 E →+* Matrix (Fin n) (Fin n) ℤ) → Module.Basis (Fin n) ℤ X := fun ρ => Classical.epsilon fun b => actMat b = ρ
  let ι := ↥hF.toFinset × ↥S
  refine hasRedCover_of_fintype (ι := ι) _ (fun x => sqForm (ref x.1.1) x.2.1) (fun x y z => ?_) (fun x y => ?_) fun B hB => ?_
  · simp only [sqForm_apply, mul_comm]
  · simp only [sqForm_apply]; exact mul_self_nonneg _
  obtain ⟨b, d, d', u, B', h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_adapted_siegel_basis_balanced_forms E H X B₀ hB₀ hB₀' n hn B hB
  have hρ : (actMat b : 𝓞 E →+* _) ∈ hF.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨d', u, h2, h3, fun c => actMat_balanced b h4 h6 c⟩
  set ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ := actMat b with hρdef
  have href : actMat (ref ρ) = ρ := Classical.epsilon_spec (p := fun b => actMat b = ρ) ⟨b, rfl⟩
  obtain ⟨e, he⟩ := exists_equiv_of_actMat_eq (O := 𝓞 E) (ref ρ) b href
  obtain ⟨c, hc, hG⟩ := hS d u h1
  refine ⟨e, fun x => if x.1.1 = ρ then c x.2.1 else 0, fun x => ?_, ?_⟩
  · dsimp only; split_ifs
    · exact hc _
    · exact le_rfl
  refine (ref ρ).ext fun i => (ref ρ).ext fun j => ?_
  have hl : B (b i) (b j) = ∑ l ∈ S, c l * ((l i : ℝ) * (l j : ℝ)) := by
    rw [h5, hG]
    simp [Matrix.sum_apply, vecMulVec_apply]
  simp only [pullR_apply, LinearEquiv.coe_coe, he, hl, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (⟨ρ, hρ⟩ : ↥hF.toFinset)]
  · simp only [if_true, sqForm_basis]
    rw [← Finset.sum_coe_sort S]
    push_cast
    rfl
  · intro y _ hy
    have : y.1 ≠ ρ := fun h => hy (Subtype.ext h)
    simp [this]
  · simp

end GlobalTheory.RedTh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntMatrixTransposeNeg
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hermForm_swap_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, star_sum, star_mul', Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun hH i) j
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h, star_star]
  ring

theorem hermForm_im_antisymm : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ)
    (M : Matrix (Fin r) (Fin r) ℤ), Hm.IsHermitian →
    (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → Mᵀ = -M := by
  intro g r Hm l M hH hM
  ext i j
  have h1 := hM j i
  rw [hermForm_swap_of_isHermitian Hm hH] at h1
  have h2 := hM i j
  simp only [Complex.star_def, Complex.conj_im] at h1
  have : ((M j i : ℤ) : ℝ) = ((-M i j : ℤ) : ℝ) := by push_cast; linarith
  simpa [Matrix.transpose_apply] using Int.cast_injective this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricEqConstMulRiemannFormOnExpChart
section
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HodgeChart

theorem hodgeMet_eq_riem_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (n a : ℕ) (ha : a ≤ n) (g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g → (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) → ∃ κ : (E →+* ℂ) → ℝ, (∀ τ, 0 < κ τ) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, ((Hm).IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm (Hm) u u).re) ∧ (∀ v w : Fin g → ℂ, ex x v = 1 → ex x w = 1 → ∃ m : ℤ, (hermForm (Hm) v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (Hm) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm Hm (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (W p) (W q) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU n a ha g ch₀ ex hEC _ hIn
  classical
  obtain ⟨htarget, -, hsymmHol, hadd, hjoint, htan⟩ := hEC
  have hsrc : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ch₀.symm z ∈ ch₀.source := fun z hz =>
    ch₀.map_target (by rw [htarget]; exact hz)
  set Ω : Set (Fin n → ℂ) := {z | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} with hΩ
  have hinΩ : ∀ x ∈ ch₀.source, Inner x → ch₀ x ∈ Ω := fun x hx hI =>
    ⟨by rw [← htarget]; exact ch₀.map_source hx, (hIn x hx).1 hI⟩
  have hΩin : ∀ z ∈ Ω, Inner (ch₀.symm z) := fun z hz =>
    (hIn _ (hsrc z hz.1)).2 (by rw [ch₀.right_inv (by rw [htarget]; exact hz.1)]; exact hz.2)
  by_cases h1 : 1 ≤ Dw.p + Dw.q
  swap
  · have hm : ∀ τ : E →+* ℂ, Dw.mult τ = 0 := fun τ => by unfold Datum.mult; split_ifs <;> omega
    refine ⟨fun _ => 1, fun _ => one_pos, fun x _ _ Hm _ f Wd _ => ⟨fun τ => ?_, fun p q _ => ?_⟩⟩
    · ext i
      have h0 := hm τ
      have h2 := i.2
      omega
    · have h0 := hm p.1
      have h2 := p.2.2
      omega
  set U' := unfFam U σ with hU'def
  have hU' : Formalism.L2.PjFree.IsUnf U' := by rw [hU'def, unfFam_self]; exact hU
  obtain ⟨W, hinj⟩ := exists_unfWit_inj hσ hU' h1
  obtain ⟨d, hdpos, hd⟩ := _root_.GlobalTheory.HodgeSmooth.exists_diag_riem_orth E H Dw l Xo c σ _ U' hσ hU' W
  have hreach : ∀ z ∈ Ω, ∃ (k : U'.Comp) (x : (U'.X k).dom), IsOrth (U'.X k) x.1 ∧
      cxPt T.Z (U'.un k x) = ch₀.symm z :=
    fun z hz => exists_orth (Z := T.Z) hσ hU' (hΩin z hz)
  by_cases hne : Ω.Nonempty
  swap
  · exact ⟨fun _ => 1, fun _ => one_pos, fun x hx hI => absurd ⟨ch₀ x, hinΩ x hx hI⟩ hne⟩
  obtain ⟨z₁, hz₁⟩ := hne
  have hreach' : ∀ z, ∃ k : U'.Comp, z ∈ Ω → ∃ x : (U'.X k).dom, IsOrth (U'.X k) x.1 ∧
      cxPt T.Z (U'.un k x) = ch₀.symm z := fun z => by
    by_cases h : z ∈ Ω
    · obtain ⟨k, x, hx⟩ := hreach z h
      exact ⟨k, fun _ => ⟨x, hx⟩⟩
    · exact ⟨(hreach z₁ hz₁).choose, fun h' => absurd h' h⟩
  choose comp hcomp using hreach'
  letI : TopologicalSpace U'.Comp := ⊥
  haveI : DiscreteTopology U'.Comp := ⟨rfl⟩
  have hcont : ContinuousOn comp Ω := by
    intro z hz
    obtain ⟨x₀, -, hx₀⟩ := hcomp z hz
    have hs0 : cxPt T.Z (U'.un (comp z) x₀) ∈ ch₀.source := by rw [hx₀]; exact hsrc z hz.1
    obtain ⟨B, hBo, hzB, hB⟩ := _root_.GlobalTheory.HodgeSmooth.chart_comp_locconst E H Dw l Xo c O β T.Z σ _ U' hσ hU' h1 n ch₀ hsymmHol (comp z) x₀ hs0
    rw [hx₀, ch₀.right_inv (by rw [htarget]; exact hz.1)] at hzB
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hBo.mem_nhds hzB)] with w hw hwB
    obtain ⟨x, -, hx⟩ := hcomp w hw
    exact hB w hwB _ x hx
  have hconst : ∀ z ∈ Ω, comp z = comp z₁ := fun z hz =>
    (_root_.GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero n a ha).constant hcont hz hz₁
  refine ⟨fun τ => if 0 < d (comp z₁) τ then 2 * Real.pi / d (comp z₁) τ else 1, fun τ => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact div_pos Real.two_pi_pos h
    · exact one_pos
  intro x hx hI Hm hHm f Wd hW
  have hz := hinΩ x hx hI
  obtain ⟨x', hx'o, hx'⟩ := hcomp _ hz
  rw [ch₀.left_inv hx] at hx'
  have hk := hconst _ hz
  have hExpAt : IsExpAt T.Z.t (x.1 ≫ genι T.Z) (ex x) := ⟨hadd x hx, (htan x hx).1, (htan x hx).2⟩
  have hslice : IsHolTo Set.univ (fun w => (ex x w).left) := by
    have hmem : ch₀ x ∈ ch₀.target := ch₀.map_source hx
    have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (ch₀ x, w)) hjoint isOpen_univ
      ((differentiableOn_const (ch₀ x)).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hmem (Set.mem_univ w)
    dsimp only at this
    rw [ch₀.left_inv hx] at this
    exact this
  obtain ⟨hg, ho⟩ := _root_.GlobalTheory.HodgeInteriorGram.gram_eq_riem E H Dw l Xo c O β T.Z σ U hσ hU W hinj d hdpos hd g x (ex x) hI hExpAt hslice _ x' hx'o hx'
    Hm hHm.2.2.1 hHm.2.2.2 f Wd hW
  refine ⟨fun τ => ?_, ho⟩
  rw [hg τ]
  by_cases hm : Dw.mult τ = 0
  · ext i
    have h2 := i.2
    omega
  · have hpos := hdpos _ x' hx'o τ (Nat.pos_of_ne_zero hm)
    have e : d (comp (ch₀ x)) τ = d (comp z₁) τ := by rw [hk]
    rw [e] at hpos ⊢
    simp only [if_pos hpos]

end GlobalTheory.HodgeChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeGeneratorsOfLinFormEqZeroStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero : ∀ {X : Type} [AddCommGroup X] {m p : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (e : Fin p ↪ Fin m) (β : LinearMap.BilinForm ℤ X), (∀ i, 0 ≤ h (δ i)) → (∀ i, h (δ i) = 0 → i ∈ Set.range e) →
    InRCone δ β → h β = 0 → InRCone (fun k => δ (e k)) β := by
  first | exact @GlobalTheory.PolFan.inRCone_of_apply_eq_zero | exact GlobalTheory.PolFan.inRCone_of_apply_eq_zero | (intros; apply GlobalTheory.PolFan.inRCone_of_apply_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvFunEvalZAddOfLinearOnRealConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invFun_evalZ_add_of_linearOn_realCone : ∀ (O : Type) [CommRing O] (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), ψ.LinearOn v → ∀ β x : LinearMap.BilinForm ℤ X, InRCone v β → InRCone v x → ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x := by
  first | exact @GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone | exact GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone | (intros; apply GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfMulIsHomogeneousOfNeZeroRightStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHomogeneous_of_mul_isHomogeneous_of_ne_zero_right : ∀ {σ : Type} (P Q : MvPolynomial σ ℝ) (a b : ℕ), Q ≠ 0 → Q.IsHomogeneous b → (P * Q).IsHomogeneous (a + b) → P.IsHomogeneous a := by
  first | exact @GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right | exact GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right | (intros; apply GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMarkedBalancedIntFormPullbackIffSplitSurjectioStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMarkedBalancedIntForm_pullback_iff_splitSurjection : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) (X X₁ : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (s : X₁ →ₗ[O] X), (∀ a, r (s a) = a) → ∀ β : LinearMap.BilinForm ℤ X₁, IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β := by
  first | exact @GlobalTheory.PolFan.Mark.SplitPull.isMarked_pull_iff | exact GlobalTheory.PolFan.Mark.SplitPull.isMarked_pull_iff | (intros; apply GlobalTheory.PolFan.Mark.SplitPull.isMarked_pull_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemClosureSumIndecomposableFaceOfAdditiveStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_sum_indecomposable_face_of_additive : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (∀ x y, InFace bar ψ lab β x → InFace bar ψ lab β y → InFace bar ψ lab β (x + y) ∧ ψ.evalZ (x + y) = ψ.evalZ x + ψ.evalZ y) → (∀ x, InFace bar ψ lab β x → ∃ n : ℤ, ψ.evalZ x = n) → (∀ x, InFace bar ψ lab β x → x ≠ 0 → 0 < ψ.evalZ x) → ∀ x, InFace bar ψ lab β x → x ∈ AddSubmonoid.closure {y | IsIndec bar ψ lab β y} := by
  first | exact @GlobalTheory.PolFan.Mark.mem_closure_isIndec | exact GlobalTheory.PolFan.Mark.mem_closure_isIndec | (intros; apply GlobalTheory.PolFan.Mark.mem_closure_isIndec <;> assumption)
end

