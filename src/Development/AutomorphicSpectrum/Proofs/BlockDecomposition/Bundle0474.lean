module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactModNearOfFiltration
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfLinearReductive
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0376
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0169
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalCompactFundamentalDomain
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.StrongUnip

open GlobalTheory.UnipFlagCore (fam wt raise fam_st)
open GlobalTheory.UAut

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def adjF : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) →+ Matrix (Fin n) (Fin n) (Af F ⊗[F] E) where
  toFun X := J⁻¹.map (inclR (F := F) (Af F)) * cT (sigR (Af F) σ) X * J.map (inclR (F := F) (Af F))
  map_zero' := by simp [cT]
  map_add' X Y := by simp [cT, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

def finM : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) →+* Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
  RingHom.mapMatrix (finT (F := F) (E := E)).toRingHom

omit [NumberField E] in
theorem finM_apply (X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (i j : Fin n) : finM X i j = finT (X i j) := rfl

omit [NumberField E] in
theorem finT_inclR (x : E) : finT (inclR (F := F) (AF F) x) = inclR (F := F) (Af F) x := by
  show Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x
  simp

omit [NumberField E] in
theorem finT_sigR (x : AF F ⊗[F] E) : finT (sigR (AF F) σ x) = sigR (Af F) σ (finT x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [NumberField E] in
theorem finM_adjA (X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) : finM (adjA σ J X) = adjF σ J (finM X) := by
  have a : ∀ M : Matrix (Fin n) (Fin n) E, finM (M.map (inclR (F := F) (AF F))) = M.map (inclR (F := F) (Af F)) :=
    fun M => by
      ext i j
      rw [finM_apply, Matrix.map_apply, Matrix.map_apply, finT_inclR]
  have b : finM (cT (sigR (AF F) σ) X) = cT (sigR (Af F) σ) (finM X) := by
    ext i j
    simp only [finM_apply, cT, Matrix.transpose_apply, Matrix.map_apply, finT_sigR]
  rw [adjA_apply, map_mul, map_mul, a, a, b]
  rfl

omit [NumberField E] in
theorem mat_projFin (g : GAd σ J) : (matHom _ σ J (projFin σ J g)).1 = finM (matHom _ σ J g).1 := by
  ext r s
  exact GlobalTheory.AutFunCompare.mat_mapH σ J (sndA F) g r s

end SlopeTestRemainingChoices

theorem strong_approx_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ W ∈ 𝓝 (1 : GFin σ J), ∃ Q : Set (GAd σ J), IsCompact Q ∧ ∀ m ∈ unipRad σ J Cc, ∃ γ ∈ ratPts σ J, ∃ q ∈ Q, q ∈ unipRad σ J Cc ∧ projFin σ J q ∈ W ∧ m = γ * q := by
  intro F E _ _ _ _ _ σ hcm n J hJ k Cc hC W hW
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.UnipFlagCore.conj_invol hcm
  obtain ⟨L, hL, hLL⟩ := exists_dualCols hJ hσ hC
  obtain ⟨d, hdd⟩ : ∃ d : Fin k → ℕ, d = fun _ => 0 := ⟨_, rfl⟩
  have hd : ∀ j, d j < 1 := fun j => by rw [hdd]; exact Nat.one_pos
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have he := idemA_complete hJ Cc L hL hC.2 hLL
  have hs := fam_st (adjA_mul hJ) (adjA_adjA hJ hσ) (idemA (F := F) Cc L) d 1
  have hcont : Continuous (adjA σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose).matrix_mul continuous_const
  have hcontF : Continuous (adjF σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Af F) σ)).matrix_transpose).matrix_mul continuous_const
  have hst0 : ∀ x ∈ (φ.mapMatrix (m := Fin n)).range, adjA σ J x ∈ (φ.mapMatrix (m := Fin n)).range := by
    rintro _ ⟨X, rfl⟩; exact ⟨_, (adjA_map X).symm⟩
  have hmem := mem_unipFlag_iff_raise hJ hσ Cc L hL hC.2 hLL hd
  have hadj1 : adjF σ J 1 = 1 := by
    have h1 := finM_adjA σ J (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
    rw [GlobalTheory.TwoStepUnipotent.st_one (adjA_mul hJ) (adjA_adjA hJ hσ), map_one] at h1
    exact h1.symm
  let fF : GFin σ J → _ := fun g => Units.embedProduct _ (matHom _ σ J g)
  have hfF : Topology.IsInducing fF := Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
  obtain ⟨O, hO, hOW⟩ := Filter.mem_comap.1 (hfF.nhds_eq_comap 1 ▸ hW)
  let G : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → _ := fun x => (x, MulOpposite.op (adjF σ J x))
  have hG : Continuous G := continuous_id.prodMk (MulOpposite.continuous_op.comp hcontF)
  have hD : G ⁻¹' O ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    hG.continuousAt.preimage_mem_nhds (by
      have : G 1 = fF 1 := Prod.ext rfl (by
        show MulOpposite.op (adjF σ J 1) = MulOpposite.op 1
        rw [hadj1])
      rw [this]; exact hO)
  have hproj : ∀ g : GAd σ J, finM (matHom _ σ J g).1 ∈ G ⁻¹' O → projFin σ J g ∈ W := fun g hg => hOW (by
    have e : fF (projFin σ J g) = G (finM (matHom _ σ J g).1) := by
      refine Prod.ext (mat_projFin σ J g) ?_
      show MulOpposite.op (matHom _ σ J (projFin σ J g)⁻¹).1 = MulOpposite.op (adjF σ J _)
      rw [← map_inv, mat_projFin, ← finM_adjA]
      congr 2
      exact (adjA_mat hJ g).symm
    show fF (projFin σ J g) ∈ O
    rw [e]; exact hg)
  obtain ⟨V, hV, H⟩ := compact_mod_near_of_weights (st := adjA σ J) (w := wt d 1)
    (ε := fam (adjA σ J) (idemA Cc L)) (φ.mapMatrix (m := Fin n)).range
    (Matrix.scalar _ (φ (1 / 2))) hcont (adjA_mul hJ) (adjA_adjA hJ hσ) hst0
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h]⟩
    (by rw [← map_add (f := _), ← map_add (f := _), add_halves, map_one, map_one])
    (fun x => (Matrix.scalar_commute _ (fun _ => Commute.all _ _) x).eq) he
    (by
      have hu : ∀ j, idemA (F := F) Cc L j ∈ (φ.mapMatrix (m := Fin n)).range := fun j => ⟨_, rfl⟩
      have hv : ∀ j : Fin k ⊕ Fin k, Sum.elim (idemA (F := F) Cc L) (fun j => adjA σ J (idemA Cc L j)) j ∈
          (φ.mapMatrix (m := Fin n)).range := by
        rintro (j | j)
        exacts [hu j, hst0 _ (hu j)]
      rintro (_ | j)
      exacts [sub_mem (one_mem _) (sum_mem fun j _ => hv j), hv j]) hs
    finM (adjF σ J) hcontF (finM_adjA σ J) _ hD
  obtain ⟨W₀, hW₀, hW₀V⟩ := exists_entry_nhds V hV
  obtain ⟨K, hK, hKW, hKs⟩ := fine_cover (E := E) W₀ hW₀
  obtain ⟨K', hK', hKD, k1, k2⟩ := H (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K)
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK)
    (fun x hx => hW₀V _ fun i j => hKW _ (hx i trivial j trivial))
    (fun X => by
      choose y hy using fun i j => hKs (X i j)
      exact ⟨_, ⟨Matrix.of y, rfl⟩, fun i _ j _ => hy i j⟩)
  let lift : ∀ x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (adjA σ J x * x = 1 ∧ x * adjA σ J x = 1) ∧
      x - 1 ∈ raise (fam (adjA σ J) (idemA Cc L)) (wt d 1) 0 → unipFlag σ J Cc d := fun x hx =>
    ⟨⟨⟨x, adjA σ J x, hx.1.2, hx.1.1⟩, (adjA_mul_self_iff hJ _).1 hx.1.1⟩, (hmem _).2 hx.2⟩
  let f : unipFlag σ J Cc d → _ := fun m => Units.embedProduct _ (matHom _ σ J m.1)
  have hf : Topology.IsInducing f :=
    Units.isInducing_embedProduct.comp (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  have hconst : unipFlag σ J Cc d = unipRad σ J Cc := by rw [hdd]; exact unipFlag_const Cc 0
  refine ⟨Subtype.val '' (f ⁻¹' ((fun x => (x, MulOpposite.op (adjA σ J x))) '' K')),
    (hf.isCompact_preimage' (hK'.image (continuous_id.prodMk (MulOpposite.continuous_op.comp hcont))) ?_).image
      continuous_subtype_val, fun m hm => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨lift x (k1 x hx), rfl⟩
  · rw [← hconst] at hm
    have hu := (adjA_mul_self_iff hJ _).2 m.2
    obtain ⟨γ, ⟨a, ha⟩, p1, k, hk, p2⟩ := k2 (matHom _ σ J m).1 ⟨⟨hu, mul_eq_one_comm.1 hu⟩, (hmem _).1 hm⟩
    obtain ⟨b, hb⟩ := hst0 γ ⟨a, ha⟩
    have e : (⟨m, hm⟩ : unipFlag σ J Cc d) = lift γ p1 * lift k (k1 k hk) := Subtype.ext (Subtype.ext (Units.ext p2))
    refine ⟨(lift γ p1).1, ?_, (lift k (k1 k hk)).1, ⟨lift k (k1 k hk), ⟨k, hk, rfl⟩, rfl⟩,
      hconst ▸ (lift k (k1 k hk)).2, hproj _ (hKD k hk), congrArg Subtype.val e⟩
    have inj : Function.Injective (φ.mapMatrix (m := Fin n)) := Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective
    have hab : a * b = 1 := inj (by rw [map_mul, ha, hb, map_one, p1.1.2])
    refine ⟨⟨a, b, hab, mul_eq_one_comm.1 hab⟩, inj ?_, Units.ext ha⟩
    have hγ' : cT (sigR (AF F) σ) γ * J.map φ * γ = J.map φ := (lift γ p1).1.2
    rw [← ha] at hγ'
    rw [map_mul, map_mul]
    exact (congrArg (· * J.map φ * a.map φ) (GlobalTheory.AutFunCounterexample.cT_map_gen σ a).symm).trans hγ'

end GlobalTheory.CompanionTheory.StrongUnip

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFrobeniusReciprocity
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.FrobRec

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def coeffMap (ρ : Representation ℂ G V) (lam : Module.Dual ℂ V) : V →ₗ[ℂ] (G → ℂ) where
  toFun v g := lam (ρ g v)
  map_add' v w := by
    funext g
    simp
  map_smul' c v := by
    funext g
    simp

theorem coeffMap_apply (ρ : Representation ℂ G V) (lam : Module.Dual ℂ V) (v : V) (g : G) :
    coeffMap ρ lam v g = lam (ρ g v) := rfl

theorem coeffMap_equivariant (ρ : Representation ℂ G V) (lam : Module.Dual ℂ V) (g : G) (v : V) :
    coeffMap ρ lam (ρ g v) = rightReg ℂ G ℂ g (coeffMap ρ lam v) := by
  funext x
  change lam (ρ x (ρ g v)) = lam (ρ (x * g) v)
  rw [map_mul, Module.End.mul_apply]

theorem coeffMap_injective {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) {lam : Module.Dual ℂ V}
    (hlam : lam ≠ 0) : Function.Injective (coeffMap ρ lam) := by
  let S : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker (coeffMap ρ lam)
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        rw [coeffMap_equivariant, hv, map_zero] }
  rcases hρ.eq_bot_or_eq_top S with h | h
  · have h1 : LinearMap.ker (coeffMap ρ lam) = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact LinearMap.ker_eq_bot.1 h1
  · exfalso
    have h1 : LinearMap.ker (coeffMap ρ lam) = ⊤ := congrArg Subrepresentation.toSubmodule h
    refine hlam (LinearMap.ext fun v => ?_)
    have h2 : v ∈ LinearMap.ker (coeffMap ρ lam) := h1 ▸ Submodule.mem_top
    have h3 := congrFun (LinearMap.mem_ker.1 h2) 1
    simpa [coeffMap_apply] using h3

end Abstract

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem chiDeltaU_mul_uni {m : ℕ} (q : ℕ) (α : Fin m → ℂ) {t u : GU σ n}
    (ht : IsDiagM (t : GL (Fin n) L)) (hu : IsUniM (u : GL (Fin n) L)) :
    chiDeltaU q α (t * u) = chiDeltaU q α t := by
  have h : ∀ i : Fin n, (((t * u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    intro i
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · rw [hu.2 i, mul_one]
    · intro j _ hj
      rw [ht i j (Ne.symm hj), zero_mul]
    · simp
  unfold chiDeltaU
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [h]
  · rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem form_uni {ρ : Representation ℂ (GU σ n) V} {lam : Module.Dual ℂ V}
    (hJ : ∀ x ∈ jacU ρ, lam x = 0) {u : GU σ n} (hu : IsUniM (u : GL (Fin n) L)) (w : V) :
    lam (ρ u w) = lam w := by
  have h : ρ u w - w ∈ jacU ρ := Submodule.subset_span ⟨u, hu, w, rfl⟩
  have h0 := hJ _ h
  rwa [map_sub, sub_eq_zero] at h0

theorem coeffMap_mem (hsplit : BorelSplitU) (hσ : ∀ x, σ (σ x) = x) {q : ℕ} {β : Fin (n / 2) → ℂˣ}
    {ρ : Representation ℂ (GU σ n) V} {lam : Module.Dual ℂ V} (hJ : ∀ x ∈ jacU ρ, lam x = 0)
    (hT : ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ∀ v,
      lam (ρ t v) = chiDeltaU q (fun i => (β i : ℂ)) t * lam v) (v : V) :
    coeffMap ρ lam v ∈ psSpaceU σ q β := by
  intro b g hb
  obtain ⟨t, u, ht, hu, rfl⟩ := hsplit L σ n hσ b hb
  rw [chiDeltaU_mul_uni q _ ht hu, coeffMap_apply, coeffMap_apply, map_mul, map_mul,
    Module.End.mul_apply, Module.End.mul_apply, hT t ht, form_uni hJ hu]

end U

theorem frobU_of_split (hsplit : BorelSplitU) : FrobU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hU _ hIrr hSat β lam hJ hlam hT
  have hmem := coeffMap_mem hsplit hU.1 hJ hT
  have hinj := coeffMap_injective hIrr hlam
  have heq := coeffMap_equivariant ρ lam
  refine ⟨?_, (coeffMap ρ lam).codRestrict (psSpaceU σ q β) hmem, ?_, fun g v => ?_⟩
  · obtain ⟨v₀, hv₀⟩ := hSat.exists_vec
    have h0 : coeffMap ρ lam v₀ ≠ 0 := fun h => hv₀.1 (hinj (h.trans (map_zero _).symm))
    have hα : IsSatVecU ϖ q (rightReg ℂ _ ℂ) (coeffMap ρ lam v₀) α := hv₀.map hU _ heq h0
    have hsph : IsSphericalU q (fun i => (β i : ℂ)) (coeffMap ρ lam v₀) := by
      intro b g k hb hk
      have h1 : coeffMap ρ lam v₀ (b * g * k) = coeffMap ρ lam v₀ (b * g) := by
        rw [coeffMap_apply, coeffMap_apply, map_mul (ρ) (b * g) k, Module.End.mul_apply,
          GlobalTheory.LGrp.mem_fixed.1 hv₀.2.1 k hk]
      rw [h1]
      exact hmem v₀ b g hb
    exact hα.unique hU (isSatVecU_of_isSphericalU hU hsph h0)
  · intro a b hab
    exact hinj (congrArg Subtype.val hab)
  · exact Subtype.ext (heq g v)

theorem frobU : FrobU := frobU_of_split _root_.GlobalTheory.CompanionTheory.BorelSplit.borelSplitU

end GlobalTheory.CompanionTheory.FrobRec

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryKTypeFinite
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}


open scoped Classical in
def toGL (M : Matrix (Fin a) (Fin a) (ι → ℂ)) : GL (Fin a) (ι → ℂ) :=
  if h : IsUnit M then h.unit else 1

theorem coe_toGL {M : Matrix (Fin a) (Fin a) (ι → ℂ)} (h : IsUnit M) : (toGL M : Matrix (Fin a) (Fin a) (ι → ℂ)) = M := by
  simp [toGL, h]

theorem toGL_coe (u : GL (Fin a) (ι → ℂ)) : toGL (u : Matrix (Fin a) (Fin a) (ι → ℂ)) = u :=
  Units.ext (coe_toGL u.isUnit)

def blkRep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : Fin a × ι ≃ Fin n)
    (σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  σ (toGL (unblk e g))

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem blkRep_blk (e : Fin a × ι ≃ Fin n) (σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)) (u : GL (Fin a) (ι → ℂ)) :
    blkRep e σ (blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ))) = σ u := by
  rw [blkRep, unblk_blk, toGL_coe]

theorem blk_coe_mem (e : Fin a × ι ≃ Fin n) (u : GL (Fin a) (ι → ℂ)) :
    blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ)) ∈ blkG e := ⟨_, u.isUnit, rfl⟩

theorem exists_gl_of_mem (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ blkG e) :
    ∃ u : GL (Fin a) (ι → ℂ), g = blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ)) := by
  obtain ⟨M, hM, rfl⟩ := hg
  exact ⟨hM.unit, rfl⟩

theorem continuousOn_toGL_unblk (e : Fin a × ι ≃ Fin n) :
    ContinuousOn (fun g => toGL (unblk e g) : Matrix (Fin n) (Fin n) ℂ → GL (Fin a) (ι → ℂ)) (blkG e) := by
  rw [continuousOn_iff_continuous_restrict]
  have hval : ∀ g : blkG e, ((toGL (unblk e g.1) : GL (Fin a) (ι → ℂ)) : Matrix (Fin a) (Fin a) (ι → ℂ)) = unblk e g.1 := by
    rintro ⟨_, M, hM, rfl⟩
    rw [unblk_blk]
    exact coe_toGL hM
  have hinv : ∀ g : blkG e, (((toGL (unblk e g.1))⁻¹ : GL (Fin a) (ι → ℂ)) : Matrix (Fin a) (Fin a) (ι → ℂ)) =
      unblk e (g.1.det⁻¹ • g.1.adjugate) := by
    rintro ⟨_, M, hM, rfl⟩
    have h := blk_inv e hM
    rw [Matrix.inv_def, Ring.inverse_eq_inv'] at h
    simp only [h, unblk_blk]
    rw [Matrix.coe_units_inv, coe_toGL hM]
  have hdet : ∀ g : blkG e, g.1.det ≠ 0 := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).1 ((mem_blkG_iff e).1 g.2).1).ne_zero
  have hc : Continuous fun g : blkG e => g.1.det⁻¹ • g.1.adjugate :=
    (Continuous.inv₀ continuous_subtype_val.matrix_det hdet).smul continuous_subtype_val.matrix_adjugate
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_unblk e).comp continuous_subtype_val).congr fun g => (hval g).symm
  · exact ((continuous_unblk e).comp hc).congr fun g => (hinv g).symm

theorem isURepOn_blkRep (e : Fin a × ι ≃ Fin n) {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)} (hσ : IsUnitaryRep σ) :
    Formalism.MainNotions.S.IsURepOn (blkG e) (blkRep e σ) := by
  refine ⟨⟨?_, ?_⟩, fun g _ v => hσ.norm_apply _ v, fun v =>
    (hσ.continuous_apply v).comp_continuousOn (continuousOn_toGL_unblk e)⟩
  · have h := blkRep_blk e σ 1
    simpa using h
  · intro g hg h hh
    obtain ⟨u, rfl⟩ := exists_gl_of_mem e hg
    obtain ⟨v, rfl⟩ := exists_gl_of_mem e hh
    rw [← blk_mul, ← Units.val_mul, blkRep_blk, blkRep_blk, blkRep_blk, map_mul]
    rfl

theorem isIrredOn_blkRep (e : Fin a × ι ≃ Fin n) {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)}
    (hi : IsTopIrreducible σ) : Formalism.MainNotions.S.IsIrredOn (blkG e) (blkRep e σ) := fun S hS hinv =>
  hi.2 S ⟨hS, fun u v hv => by
    have h := hinv _ (blk_coe_mem e u) v hv
    rwa [blkRep_blk] at h⟩

theorem blk_mem_maxCpt (e : Fin a × ι ≃ Fin n) (k : Matrix.unitaryGroup (Fin a) (ι → ℂ)) :
    blk e k.1 ∈ GlobalTheory.LinRed.maxCpt (blkG e) := by
  refine ⟨blk_coe_mem e (Unitary.toUnits k), ?_⟩
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← blk_conjTranspose, ← blk_mul,
    ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff).1 k.2, blk_one]

theorem exists_unitary_of_mem_maxCpt (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ GlobalTheory.LinRed.maxCpt (blkG e)) :
    ∃ k : Matrix.unitaryGroup (Fin a) (ι → ℂ), g = blk e k.1 := by
  obtain ⟨⟨M, -, rfl⟩, hu⟩ := hg
  refine ⟨⟨M, ?_⟩, rfl⟩
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← blk_conjTranspose, ← blk_mul,
    ← blk_one e, ← Matrix.star_eq_conjTranspose] at hu
  rw [Matrix.mem_unitaryGroup_iff]
  exact blk_injective e hu

theorem finiteDimensional_isoPart_gl [CompleteSpace H] {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)}
    (hσ : IsUnitaryRep σ) (hi : IsTopIrreducible σ) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin a) (ι → ℂ)) W) :
    FiniteDimensional ℂ (isoPart (σ.comp Unitary.toUnits) ρ) := by
  let e := Fintype.equivFin (Fin a × ι)
  have hLR : GlobalTheory.LinRed.IsLinRed (blkG e) := by
    refine
      { one_mem := ⟨1, isUnit_one, blk_one e⟩
        mul_mem := ?_
        isUnit := fun g hg => ((mem_blkG_iff e).1 hg).1
        inv_mem := ?_
        closed := fun g hg hcl => (mem_blkG_iff e).2 ⟨hg, blk_unblk_of_mem_closure e hcl⟩
        connected := isPreconnected_blkG e
        star_mem := ?_ }
    · rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
      exact ⟨M * N, IsUnit.mul hM hN, blk_mul e M N⟩
    · rintro _ ⟨M, hM, rfl⟩
      exact ⟨M⁻¹, (Matrix.isUnit_nonsing_inv_iff).2 hM, (blk_inv e hM).symm⟩
    · rintro _ ⟨M, hM, rfl⟩
      exact ⟨Mᴴ, IsUnit.star hM, blk_conjTranspose e M⟩
  have hA := GlobalTheory.CompanionTheory.admitted.isAdmissible_of_unitary_irreducible hLR
    (GlobalTheory.CompanionTheory.AdmIwa.RamifiedPrimeLengthBound hLR (GlobalTheory.CompanionTheory.IwaGen.iwaOn_of_isLinRed hLR)) H (blkRep e σ)
    (isURepOn_blkRep e hσ) (isIrredOn_blkRep e hi)
  have hrep : ∀ k : Matrix.unitaryGroup (Fin a) (ι → ℂ),
      blkRep e σ (blk e k.1) = (σ.comp Unitary.toUnits) k := fun k => blkRep_blk e σ (Unitary.toUnits k)
  refine finiteDimensional_isoPart (π := σ.comp Unitary.toUnits) (fun k v => hσ.norm_apply _ v) ?_ _ W ρ rfl
  intro S hfd hS hirr
  have hKS : GlobalTheory.LinRed.IsKStable (blkG e) (blkRep e σ) S := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := exists_unitary_of_mem_maxCpt e hg
    rw [hrep]
    exact hS k w hw
  have hirr' : ∀ S' : Submodule ℂ H, S' ≤ S → GlobalTheory.LinRed.IsKStable (blkG e) (blkRep e σ) S' → S' = ⊥ ∨ S' = S :=
    fun S' hle hst => hirr S' hle fun k w hw => by
      have h := hst _ (blk_mem_maxCpt e k) w hw
      rwa [hrep] at h
  have hfin := hA.2.2.2 S hfd hKS hirr'
  have heq : {S' : Submodule ℂ H | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
      ∀ k, ∀ w ∈ S, T ((σ.comp Unitary.toUnits) k w) = (σ.comp Unitary.toUnits) k (T w)} =
      {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k ∈ GlobalTheory.LinRed.maxCpt (blkG e), ∀ w ∈ S,
        T (blkRep e σ k w) = blkRep e σ k (T w)} := by
    ext S'
    constructor
    · rintro ⟨T, rfl, hT⟩
      refine ⟨T, rfl, fun g hg w hw => ?_⟩
      obtain ⟨k, rfl⟩ := exists_unitary_of_mem_maxCpt e hg
      rw [hrep]
      exact hT k w hw
    · rintro ⟨T, rfl, hT⟩
      refine ⟨T, rfl, fun k w hw => ?_⟩
      rw [← hrep]
      exact hT _ (blk_mem_maxCpt e k) w hw
  rw [heq]
  exact hfin

theorem admissible_GL_Cinf : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : GL (Fin a) (Cinf E) →* (H →L[ℂ] H)), IsUnitaryRep σ → IsTopIrreducible σ → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), FiniteDimensional ℂ ↥(⨆ (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = σ (Unitary.toUnits k) (T w)), LinearMap.range T : Submodule ℂ H) := by
  intro E _ _ _ a H _ _ _ σ hσ hi W _ _ _ ρ
  classical
  exact finiteDimensional_isoPart_gl hσ hi ρ

end GlobalTheory.CompanionTheory.AdmGL

end
end

