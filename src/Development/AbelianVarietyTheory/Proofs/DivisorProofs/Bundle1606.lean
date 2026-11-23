module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeVertexLatticeGridCorner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem isLattice_comap_gl {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : Type} [Fintype n] [DecidableEq n]
    (g : GL n K) (M : Submodule R (n → K)) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (M.comap (g.1.mulVecLin.restrictScalars R)) := by
  let e : (n → K) ≃ₗ[K] (n → K) := LinearEquiv.ofLinear g.1.mulVecLin (g⁻¹).1.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one])
  have h : M.comap (g.1.mulVecLin.restrictScalars R) = M.map ((e.symm : (n → K) →ₗ[K] (n → K)).restrictScalars R) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      have : e (e.symm y) ∈ M := by rw [e.apply_symm_apply]; exact hy
      exact this
  rw [h]
  refine ⟨hM.fg.map _, ?_⟩
  have h2 : ((M.map ((e.symm : (n → K) →ₗ[K] (n → K)).restrictScalars R) : Submodule R (n → K)) : Set (n → K)) =
      (e.symm : (n → K) →ₗ[K] (n → K)) '' (M : Set (n → K)) := rfl
  intro s hs hi
  rw [h2] at hs
  have hs' : e '' s ⊆ (M : Set (n → K)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hs hx
    simpa [← hyx] using hy
  have hi' : LinearIndepOn R id (e '' s) :=
    (linearIndepOn_id_imageₛ_iff (f := (e : (n → K) →ₗ[K] (n → K)).restrictScalars R)
      (show Function.Injective ((e : (n → K) →ₗ[K] (n → K)).restrictScalars R) from e.injective).injOn).2 hi
  have hk := hM.linearIndepOn (e '' s) hs' hi'
  have hk' := (linearIndepOn_id_imageₛ_iff (f := (e.symm : (n → K) →ₗ[K] (n → K)))
    (show Function.Injective (e.symm : (n → K) →ₗ[K] (n → K)) from e.symm.injective).injOn).2 hk
  change LinearIndepOn K id (e.symm '' (e '' s)) at hk'
  simpa [Set.image_image] using hk' 

theorem _root_.GlobalTheory.T.isLattice_vertexLattice_gridCorner : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ)
    (y : FinPt G (.grid D.R.m D.R.m)), Submodule.IsLattice D.host.E (GlobalTheory.SumSize.latAt S (.grid D.R.m D.R.m) y) := by
  intro D T L sc G W S y
  have hm := D.R.two_le_m
  have hΛ : Submodule.IsLattice D.host.E (G.Λ (.grid D.R.m D.R.m)) :=
    (G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by
      have : D.R.m = 0 := (Node.grid.inj e).1
      omega).sd.1
  apply isLattice_comap_gl _ _
  apply Submodule.IsLattice.of_fg
  obtain ⟨c, hc, hu⟩ := Formalism.UG.P.adelstabL_upper (F := D.host.F) _ (Module.Finite.iff_fg.2 hΛ.fg)
  obtain ⟨d, hd, c', hc', hcg, hcgi⟩ := Formalism.UG.P.levelaf_exists_denom (E := D.host.E) (finG (G.V (.grid D.R.m D.R.m)) y)
  have hG := Formalism.UG.P.adelstab_entries (finG (G.V (.grid D.R.m D.R.m)) y) d c' hc' hcg
  exact Module.Finite.iff_fg.mp (Formalism.UG.P.adelstab_finite (finG (G.V (.grid D.R.m D.R.m)) y) _ c d hc hd hu hG)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMovedRiggingIs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open GlobalTheory.Mem.Isom
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Rig)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.TriMove

variable {D : D7} {S S' : HSp D}

theorem rdx_conj_diag {m n : ℕ} (h : m = n) (d : Fin m → ℂ) :
    (rdx (K := ℂ) h)ᴴ * diagonal d * rdx (K := ℂ) h = diagonal (d ∘ (finCongr h).symm) := by
  subst h
  ext i j
  simp [rdx, Matrix.one_apply, Matrix.diagonal_apply]

theorem diag_rdx {m n : ℕ} (h : m = n) (d : Fin m → ℂ) :
    diagonal d * rdx (K := ℂ) h = rdx (K := ℂ) h * diagonal (d ∘ (finCongr h).symm) := by
  subst h
  ext i j
  simp only [rdx, finCongr_refl, Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id, Matrix.mul_one, Matrix.one_mul,
    Function.comp_id]

theorem rdi_mulVec {K : Type} [CommRing K] {m n : ℕ} (h : m = n) (v : Fin m → K) (i : Fin n) :
    (rdi (K := K) h *ᵥ v) i = v ((finCongr h).symm i) := by
  subst h
  simp [rdi, Matrix.one_apply]

theorem cT_sig_eq (M : Matrix (Fin S'.rank) (Fin S.rank) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := by
  ext i j
  rfl

theorem mem_latMove (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (y : Fin S'.rank → D.host.E) :
    y ∈ latMove I Λ ↔ I.Q *ᵥ y ∈ Λ := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    show I.Q *ᵥ (I.P *ᵥ u) ∈ Λ
    rwa [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec]
  · intro hy
    refine ⟨I.Q *ᵥ y, hy, ?_⟩
    show I.P *ᵥ (I.Q *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, I.PQ, Matrix.one_mulVec]

theorem sumForm_eq (G : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_move (I : IsoMat S S') (x y : Fin S.rank → D.host.E) :
    star (I.P *ᵥ x) ⬝ᵥ (S'.gram *ᵥ (I.P *ᵥ y)) = star x ⬝ᵥ (S.gram *ᵥ y) := by
  have hg : I.Pᴴ * S'.gram * I.P = S.gram := by rw [← cT_sig_eq]; exact I.gram
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem latS_mulVec_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (T : Subring (TensorProduct F E R)) {n N : ℕ}
    (M : Matrix (Fin N) (Fin n) E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E))
    (hM : ∀ x ∈ Λ', M *ᵥ x ∈ Λ) :
    ∀ x ∈ Formalism.UG.latS (F := F) R T Λ', (M.map (Formalism.UG.inclE (F := F) R)) *ᵥ x ∈ Formalism.UG.latS (F := F) R T Λ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x0, hx0, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨M *ᵥ x0, hM x0 hx0, ?_⟩
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have e : (M.map (Formalism.UG.inclE (F := F) R)) *ᵥ (a • x) = a • ((M.map (Formalism.UG.inclE (F := F) R)) *ᵥ x) := by
      rw [Subring.smul_def, Subring.smul_def, mulVec_smul]
    rw [e]; exact Submodule.smul_mem _ a hx

theorem mem_hatL_move (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x : Fin S'.rank → Lev.EAf D) :
    x ∈ Formalism.L2.Herm.hatL (latMove I Λ) ↔ fQ I *ᵥ x ∈ Formalism.L2.Herm.hatL Λ := by
  constructor
  · intro hx
    exact latS_mulVec_mem _ _ I.Q (latMove I Λ) Λ (fun y hy => (mem_latMove I Λ y).1 hy) x hx
  · intro hx
    have h := latS_mulVec_mem _ _ I.P Λ (latMove I Λ)
      (fun y hy => (mem_latMove I Λ _).2 (by rwa [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec])) _ hx
    have e : I.P.map (Formalism.UG.inclE _) *ᵥ (fQ I *ᵥ x) = x := by
      show fP I *ᵥ (fQ I *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, fP_fQ, Matrix.one_mulVec]
    rwa [e] at h

theorem frame_inv (I : IsoMat S S') (β : GL (Fin S.rank) (Lev.EAf D)) :
    ((betaMove I β)⁻¹ : GL (Fin S'.rank) (Lev.EAf D)).val =
      HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) I.rank_eq) (β⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) (fQ I) := rfl

theorem frame_move (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (β : GL (Fin S.rank) (Lev.EAf D))
    (hβ : Formalism.L2.DIV.IsFrame β Λ) :
    Formalism.L2.DIV.IsFrame (F := D.host.F) (E := D.host.E) (n := S'.rank) (betaMove I β) (latMove I Λ) := by
  intro x
  rw [mem_hatL_move, hβ, frame_inv]
  simp only [← Matrix.mulVec_mulVec, rdi_mulVec]
  exact ⟨fun H i => H _, fun H j => by simpa using H (finCongr I.rank_eq j)⟩

theorem selfDual_move (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (h : IsSelfDualC S Λ) :
    IsSelfDualC S' (latMove I Λ) := by
  have hPQ : ∀ y, I.P *ᵥ (I.Q *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, I.PQ, Matrix.one_mulVec]
  have hQP : ∀ y, I.Q *ᵥ (I.P *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec]
  obtain ⟨hl, hd⟩ := h
  refine ⟨Submodule.IsLattice.of_fg D.host.E (hl.fg.map _), ?_⟩
  · intro y
    rw [mem_latMove, hd (I.Q *ᵥ y)]
    simp only [sumForm_eq]
    constructor
    · intro H x hx
      rw [mem_latMove] at hx
      obtain ⟨b, hb⟩ := H _ hx
      refine ⟨b, ?_⟩
      rw [hb, ← form_move I, hPQ, hPQ]
    · intro H x hx
      have hx' : I.P *ᵥ x ∈ latMove I Λ := by rw [mem_latMove, hQP]; exact hx
      obtain ⟨b, hb⟩ := H _ hx'
      refine ⟨b, ?_⟩
      rw [hb, ← form_move I, hPQ]

theorem cartan_conj {m n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} {G' : Matrix (Fin m) (Fin m) ℂ} {a : Matrix (Fin m) (Fin n) ℂ}
    {b : Matrix (Fin n) (Fin m) ℂ} (hab : a * b = 1) (hba : b * a = 1) (hb : bᴴ * G * b = G') (ha : aᴴ * G' * a = G)
    {s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCartanInv G' (a * s * b) := by
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · calc a * s * b * (a * s * b) = a * (s * (b * a) * s) * b := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hba, Matrix.mul_one, h1, Matrix.mul_one, hab]
  · rw [conjTranspose_mul, conjTranspose_mul]
    calc bᴴ * (sᴴ * aᴴ) * G' * (a * s * b) = bᴴ * (sᴴ * (aᴴ * G' * a) * s) * b := by simp only [Matrix.mul_assoc]
      _ = G' := by rw [ha, h2, hb]
  · have e : G' * (a * s * b) = bᴴ * (G * s) * b := by
      rw [← hb]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc b a, hba, Matrix.one_mul]
    rw [e]
    refine h3.conjTranspose_mul_mul_same fun u v huv => ?_
    have := congrArg (a *ᵥ ·) huv
    simpa [Matrix.mulVec_mulVec, hab] using this

theorem onb_conj {m n : ℕ} (h : n = m) {G : Matrix (Fin n) (Fin n) ℂ} {G' : Matrix (Fin m) (Fin m) ℂ}
    {a : Matrix (Fin m) (Fin n) ℂ} {b : Matrix (Fin n) (Fin m) ℂ} (hba : b * a = 1) (ha : aᴴ * G' * a = G)
    {s B : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} (hs : IsONBasis G s B p) :
    IsONBasis G' (a * s * b) (a * B * rdx (K := ℂ) h) p := by
  obtain ⟨ε, hε, hd, hsB⟩ := hs
  refine ⟨fun i => ε ((finCongr h).symm i), fun i => ?_, ?_, ?_⟩
  · simpa using hε ((finCongr h).symm i)
  · rw [conjTranspose_mul, conjTranspose_mul]
    calc (rdx (K := ℂ) h)ᴴ * (Bᴴ * aᴴ) * G' * (a * B * rdx (K := ℂ) h)
        = (rdx (K := ℂ) h)ᴴ * (Bᴴ * (aᴴ * G' * a) * B) * rdx (K := ℂ) h := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hd]; exact rdx_conj_diag h _
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b a, hba, Matrix.one_mul, ← Matrix.mul_assoc s B, hsB, Matrix.mul_assoc B, diag_rdx h]
    rfl

theorem rigMove_is {S S' : HSp D} (I : IsoMat S S') (r : Rig S) (hr : r.Is) : (rigMove I r).Is := by
  unfold Rig.Is at hr ⊢
  obtain ⟨h1, h2, h3⟩ := hr
  refine ⟨selfDual_move I r.Λ h1, frame_move I r.Λ r.β h2, fun τ => ?_⟩
  have hG' : (I.qT τ)ᴴ * gramAt D S τ * I.qT τ = gramAt D S' τ := I.qT_gram τ
  have hG : (I.pT τ)ᴴ * gramAt D S' τ * I.pT τ = gramAt D S τ := I.symm.qT_gram τ
  obtain ⟨hc, p, hp⟩ := h3 τ
  exact ⟨cartan_conj (I.pT_qT τ) (I.qT_pT τ) hG' hG hc, p, onb_conj I.rank_eq (I.qT_pT τ) hG hp⟩

end GlobalTheory.TriMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicEisensteinSeriesRationalPointsPermuteTe
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem reps_perm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → (∀ γ ∈ ratPts σ J, ∃ π : T ≃ T, ∀ (i : T) g, h (i.1.1 * (γ * g)) = h ((π i).1.1 * g)) ∧ (∃ i : T, ∀ g, h (i.1.1 * g) = h g) ∧ (∀ γ ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤), ∀ g, h (γ * g) = h g) ∧ ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D T hT
  have hrat := (_root_.GlobalTheory.ResidueEisenstein.frame_levi_facts F E σ n J r X Y D.cm D.herm D.witt).2.2.2.2.1
  have h3 : ∀ γ ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤), ∀ g, h (γ * g) = h g := by
    rintro γ ⟨hγ, B, -, hB⟩ g
    obtain ⟨p, β, hp, k, hk, rfl⟩ := D.iwa g
    have hs : ScalesBy σ J X (γ * p) (B * β) := by
      unfold ScalesBy at hp ⊢
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hp, ← Matrix.mul_assoc, hB, Matrix.mul_assoc, Units.val_mul]
    rw [← mul_assoc, D.ht _ _ hs k hk, D.ht _ _ hp k hk, map_mul, map_mul, hrat γ hγ B hB, one_mul]
  have h4 : ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) := by
    intro γ
    obtain ⟨t, ⟨ht, β, hβ⟩, hu⟩ := hT γ
    exact ⟨t, ⟨ht, (γ * t⁻¹).2, β, trivial, hβ⟩, fun s hs => hu s ⟨hs.1, let ⟨β, _, e⟩ := hs.2.2; ⟨β, e⟩⟩⟩
  refine ⟨fun γ hγ => ?_, ?_, h3, h4⟩
  · obtain ⟨π, hπ⟩ := exists_equiv_reps _ _ T h4 ⟨γ, hγ⟩
    refine ⟨π, fun i g => ?_⟩
    rw [← h3 _ (hπ i) ((π i).1.1 * g)]
    congr 1
    simp [mul_assoc]
  · obtain ⟨t, ⟨ht, hl⟩, -⟩ := h4 1
    refine ⟨⟨t, ht⟩, fun g => ?_⟩
    rw [← h3 _ hl (t.1 * g)]
    congr 1
    simp

end GlobalTheory.ResidueEisenstein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteModuleIrreducibleOfIrreducibleUnitaryRep
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KFinIrr

theorem smE_eq {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hK : IsKMod ε σ D E) (v : D) (hv : (v : H) ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (a b : Fin n) :
    ((ReciprocityTheory.ChartRestriction.DS.smE ε σ a b ⟨v, hv⟩ : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) = ((E a b v : D) : H) := by
  have hσ' : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ := hσ
  have key : ∀ X, ReciprocityTheory.ChartRestriction.DS.inG ε X →
      ReciprocityTheory.ChartRestriction.DS.dS σ X (v : H) = ∑ c, ∑ d, X c d • ((E c d v : D) : H) := fun X hX =>
    (hK.real X hX v).deriv
  rw [ReciprocityTheory.ChartRestriction.DS.smE_apply hσ']
  change ReciprocityTheory.ChartRestriction.DS.dS σ _ (v : H) + Complex.I • ReciprocityTheory.ChartRestriction.DS.dS σ _ (v : H) = _
  rw [key _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε _), key _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε _)]
  have hz : ∀ c d, ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (Matrix.single a b 1) c d +
      Complex.I * ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (Matrix.single a b 1) c d = Matrix.single a b (1 : ℂ) c d := by
    intro c d
    have := congrFun (congrFun (ReciprocityTheory.ChartRestriction.DS.SmDerA.cpart_decomp ε (Matrix.single a b 1)) c) d
    rw [this]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  calc _ = ∑ c, ∑ d, (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (Matrix.single a b 1) c d +
        Complex.I * ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (Matrix.single a b 1) c d) • ((E c d v : D) : H) := by
          simp only [Finset.smul_sum, add_smul, Finset.sum_add_distrib, smul_smul]
    _ = ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • ((E c d v : D) : H) := by simp only [hz]
    _ = ((E a b v : D) : H) := by
          simp [Matrix.single_apply, ite_smul, ite_and]

theorem kMod_irred : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ N : Submodule ℂ D, (∀ a b, ∀ x ∈ N, E a b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro n ε H _ _ σ D E hc hσ hirr hK N hN
  haveI := hc
  have hle : D ≤ ReciprocityTheory.ChartRestriction.DS.smD ε σ := fun v hv =>
    (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr).1 v ((hK.mem v).1 hv)
  let ι : D →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε σ := Submodule.inclusion hle
  have hι : Function.Injective ι := Submodule.inclusion_injective hle
  have hcomm : ∀ a b (x : D), ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (ι x) = ι (E a b x) := fun a b x =>
    Subtype.ext (smE_eq hσ hK x (hle x.2) a b)
  let N' : Submodule ℂ (ReciprocityTheory.ChartRestriction.DS.smD ε σ) := N.map ι
  have hN'K : (N' : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) ⊆ CompanionTheory.D.gk.HC.KF ε σ := by
    rintro _ ⟨x, -, rfl⟩
    exact (hK.mem x).1 x.2
  have hN'st : ∀ a b, ∀ v ∈ N', ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ N' := by
    rintro a b _ ⟨x, hx, rfl⟩
    rw [hcomm]
    exact ⟨_, hN a b x hx, rfl⟩
  rcases GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N' hN'K hN'st with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : ι x ∈ N' := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at hx'
    rw [Submodule.mem_bot]
    exact hι (by rw [hx', map_zero])
  · right
    rw [eq_top_iff]
    intro x _
    have hx' : ι x ∈ (N' : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) := by
      rw [h]
      exact (hK.mem x).1 x.2
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [hι hyx] at hy
    exact hy

end GlobalTheory.KFinIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteVectorsIrreducibleUnitaryUnitaryGroupPQ
section
open Matrix

noncomputable section

namespace GlobalTheory.KFinLinkPort

open GlobalTheory.KFinVec
open ReciprocityTheory.ChartRestriction.DS (smD smE smE_apply isDerivedOn_smE dS dS_eq_actM actM)
open CompanionTheory.D.gk.HC (KF)

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_eq_dS (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    Formalism.L2.Theta.dRep σ X w = dS σ X w := by
  unfold Formalism.L2.Theta.dRep dS
  congr 1

theorem isAdmissible_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsAdmissible ε σ := by
  rintro S ⟨hf, -, hK, -⟩
  have hfin : FiniteDimensional ℂ (Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S) :=
    (CompanionTheory.HCMult.harish_chandra_multiplicity : Formalism.MainNotions.BridgeCPX.HCMult) n ε H σ hσ hirr S hf hK
  have hle : kIsotypic ε σ S ≤ Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S :=
    iSup_le fun T => le_sSup ⟨T.1, fun a v w h => T.2 _ a.2 v w h, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem isLieStable_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsLieStable ε σ (kFinSub ε σ) := by
  intro X hX v hv
  obtain ⟨h1, h2⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  have hvS : v ∈ smD ε σ := h1 v hv
  rw [dRep_eq_dS]
  have e := dS_eq_actM (isDerivedOn_smE hσ) hX ⟨v, hvS⟩
  simp only [] at e
  rw [e]
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (h2 a b ⟨v, hvS⟩ hv)

theorem lieIrr_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (S : Submodule ℂ H) (hS : S ≤ kFinSub ε σ)
    (hL : IsLieStable ε σ S) : S = ⊥ ∨ S = kFinSub ε σ := by
  obtain ⟨h1, -⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  let N : Submodule ℂ (smD ε σ) := S.comap (smD ε σ).subtype
  have hNK : (N : Set (smD ε σ)) ⊆ KF ε σ := fun v hv => hS hv
  have hst : ∀ a b, ∀ v ∈ N, smE ε σ a b v ∈ N := by
    intro a b v hv
    show ((smE ε σ a b v : smD ε σ) : H) ∈ S
    rw [smE_apply hσ]
    have e1 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε (Matrix.single a b 1)) (v : H) hv
    have e2 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε (Matrix.single a b 1)) (v : H) hv
    rw [dRep_eq_dS] at e1 e2
    exact S.add_mem e1 (S.smul_mem _ e2)
  rcases GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N hNK hst with h | h
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hvN : (⟨v, h1 v (hS hv)⟩ : smD ε σ) ∈ N := hv
    rw [h] at hvN
    have := (Submodule.mem_bot ℂ).1 hvN
    exact (Submodule.mem_bot ℂ).2 (congrArg Subtype.val this)
  · right
    refine le_antisymm hS fun v hv => ?_
    have hvK : (⟨v, h1 v hv⟩ : smD ε σ) ∈ KF ε σ := hv
    rw [← h] at hvK
    exact hvK

end GlobalTheory.KFinLinkPort

namespace GlobalTheory.KFinLinkPort

theorem kFiniteVectors_irreducibleUnitary_unitaryGroupPQ : GlobalTheory.Published.KFiniteVectorsUnitary := by
  intro n ε H _ _ _ _ σ hσ hirr
  exact ⟨GlobalTheory.KFinLinkPort.isAdmissible_of hσ hirr,
    GlobalTheory.HcPort.kFiniteVectors_analytic_indefiniteUnitary n ε H σ hσ hirr,
    GlobalTheory.T.dense_kFinite_vectors_unitaryGroupRep n ε H σ hσ,
    GlobalTheory.KFinLinkPort.isLieStable_of hσ hirr,
    fun S hS hL => GlobalTheory.KFinLinkPort.lieIrr_of hσ hirr S hS hL⟩

end GlobalTheory.KFinLinkPort

end
end

