module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0040
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterTransport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0356
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinus
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirSmooth

section General

variable {G M V : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_twAct [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (hc : Continuous s) (hρ : IsSmooth ρ) : IsSmooth (twAct ρ N θ s hs) :=
  _root_.UpperTheory.Reformulated.B.Gwa2.isSmooth_twAct ρ N θ s hs hc hρ

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_glEmbHom (n : ℕ) : Continuous (glEmbHom k n) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun A : Matrix (Fin n) (Fin n) k => glEmbMat k n A i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa [glEmbMat] using continuous_const
    | cast j => simpa [glEmbMat] using continuous_const
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [glEmbMat] using continuous_const
    | cast j =>
      simpa [glEmbMat] using (continuous_id.matrix_elem i j)

theorem continuous_glEmb (n : ℕ) : Continuous (glEmb k n) :=
  Continuous.units_map _ (continuous_glEmbHom n)

theorem continuous_levi (n : ℕ) : Continuous (levi k n) :=
  (continuous_glEmb n).subtype_mk _

theorem smPhiMinus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    SmPhiMinus k := by
  intro ψ n V _ _ τ hτ
  exact isSmooth_twAct τ (MirUin k (n + 1)) (mirChar k ψ n) ((levi k (n + 1)).comp (Mir k n).subtype) (levi_stab ψ n)
    ((continuous_levi (n + 1)).comp continuous_subtype_val) hτ

end GlobalTheory.CompanionTheory.BZMirSmooth

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinus
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirFun

open Matrix

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_glEmbHom (n : ℕ) : Continuous (glEmbHom k n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun A : Matrix (Fin n) (Fin n) k => glEmbMat k n A i j
  induction i using Fin.lastCases with
  | last => induction j using Fin.lastCases <;> simpa [glEmbMat] using continuous_const
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [glEmbMat] using continuous_const
    | cast j =>
      simp only [glEmbMat, Fin.lastCases_castSucc]
      exact (continuous_apply j).comp (continuous_apply i)

theorem continuous_levi (n : ℕ) : Continuous (levi k n) := by
  have h : Continuous (glEmb k n) := Continuous.units_map _ (continuous_glEmbHom k n)
  exact h.subtype_mk _

theorem smPsiMinus : SmPsiMinus k :=
  by apply _root_.UpperTheory.Reformulated.B.DYhc8.main <;> assumption

end GlobalTheory.CompanionTheory.BZMirFun
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedBySmallBox
section
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

theorem exists_box_subset_of_mem_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) {U : Set (Fin n → k)} (hU : U ∈ 𝓝 (0 : Fin n → k)) :
    ∃ N : ℤ, ∀ x ∈ box k n N, Multiplicative.toAdd x ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have hball : ∀ i, ∃ N : ℤ, (valBall k N : Set k) ⊆ t i := fun i => by
    obtain ⟨N, -, hN⟩ := (hasBasis_nhds_zero_valBall (K := k)).mem_iff.mp (ht i)
    exact ⟨N, hN⟩
  choose Nf hNf using hball
  refine ⟨((Finset.univ.sup fun i => (Nf i).toNat : ℕ) : ℤ), fun x hx => hsub fun i _ => ?_⟩
  have hle : Nf i ≤ ((Finset.univ.sup fun i => (Nf i).toNat : ℕ) : ℤ) :=
    (Int.self_le_toNat (Nf i)).trans (by exact_mod_cast Finset.le_sup (f := fun i => (Nf i).toNat) (Finset.mem_univ i))
  exact hNf i (valBall_antitone hle ((mem_box k).mp hx i))

theorem exists_box_fixed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V), IsSmooth ρ →
    ∀ v : V, ∃ N : ℤ, ∀ x ∈ box k n N, ρ x v = v := by
  intro k _ _ _ _ n V _ _ ρ hρ v
  have hopen : IsOpen {y : Fin n → k | ρ (Multiplicative.ofAdd y) v = v} := hρ v
  have hU : {y : Fin n → k | ρ (Multiplicative.ofAdd y) v = v} ∈ 𝓝 (0 : Fin n → k) :=
    hopen.mem_nhds (by simp)
  obtain ⟨N, hN⟩ := exists_box_subset_of_mem_nhds k n hU
  exact ⟨N, fun x hx => by simpa using hN x hx⟩

end GlobalTheory.CompanionTheory.MirFourier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantContractsUnipotent
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc Topology Filter Matrix

namespace GlobalTheory.CompanionTheory.ExpandN

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nhdsNE_zero_neBot : (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem exists_one_add_smul_mem_unipRad {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) {u : GL n k} (hu : u ∈ unipRad k e) (c : k) :
    ∃ v : GL n k, (v : Matrix n n k) = 1 + c • ((u : Matrix n n k) - 1) ∧ v ∈ unipRad k e := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hu
  have hsame : ∀ i j, blk e i = blk e j → (u : Matrix n n k) i j = (1 : Matrix n n k) i j := by
    intro i j hij
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    obtain rfl : a = b := by simpa using hij
    rw [hD a i j, Matrix.one_apply, Matrix.one_apply]
    simp
  set M : Matrix n n k := 1 + c • ((u : Matrix n n k) - 1) with hM
  have hMsame : ∀ i j, blk e i = blk e j → M i j = (1 : Matrix n n k) i j := by
    intro i j hij
    simp [hM, hsame i j hij]
  have hT : M.BlockTriangular (blk e) := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    have h0 : (u : Matrix n n k) i j = 0 := mem_parab.1 hP i j hij
    simp [hM, h0, Matrix.one_apply_ne hne]
  have hdet : M.det = 1 := by
    rw [hT.det_fintype]
    refine Finset.prod_eq_one fun a _ => ?_
    have : M.toSquareBlock (blk e) a = 1 := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      rw [Matrix.toSquareBlock_def]
      simp only [Matrix.of_apply]
      rw [hMsame i j (hi.trans hj.symm), Matrix.one_apply, Matrix.one_apply]
      simp
    rw [this, Matrix.det_one]
  obtain ⟨v, hv⟩ : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by simp [hdet])
  refine ⟨v, hv, mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩⟩
  · rw [hv]; exact hT hij
  · rw [hv, hMsame _ _ (by simp), Matrix.one_apply, Matrix.one_apply]
    simp

theorem val_conj_one_add_smul {n : Type} [Fintype n] [DecidableEq n] (G u v : GL n k) (c : k)
    (hv : (v : Matrix n n k) = 1 + c • ((u : Matrix n n k) - 1)) :
    ((G * v * G⁻¹ : GL n k) : Matrix n n k) =
      1 + c • (((G * u * G⁻¹ : GL n k) : Matrix n n k) - 1) := by
  have h1 : (G : Matrix n n k) * ((G⁻¹ : GL n k) : Matrix n n k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul, hv, mul_add, add_mul, mul_sub, sub_mul, mul_one,
    Matrix.mul_smul, Matrix.smul_mul, h1]

theorem exists_pow_conj_mem_KN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) →
    IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t →
    ∀ n ∈ unipRad k (stdBlocks d hd), ∃ r : ℕ,
      leviEmb k (stdBlocks d hd) t ^ r * n * (leviEmb k (stdBlocks d hd) t ^ r)⁻¹ ∈ KN k N J d hd := by
  intro k _ _ _ _ N h d hd J hJo _ _ _ t ht n hn
  obtain ⟨O, hO, hOJ⟩ := (GlobalTheory.SplitFlip.isEmbedding_val_GL (k := k) (n := Fin N)).isInducing.isOpen_iff.1 hJo
  have memJ : ∀ x : GL (Fin N) k, x ∈ J ↔ (x : Matrix (Fin N) (Fin N) k) ∈ O := by
    intro x
    have : x ∈ (J : Set (GL (Fin N) k)) ↔ x ∈ (fun g : GL (Fin N) k => g.val) ⁻¹' O := by rw [hOJ]
    exact this
  have h1O : (1 : Matrix (Fin N) (Fin N) k) ∈ O := by
    simpa using (memJ 1).1 J.one_mem
  set X : Matrix (Fin N) (Fin N) k := (n : Matrix (Fin N) (Fin N) k) - 1 with hX
  haveI := nhdsNE_zero_neBot (k := k)
  have hcont : Continuous fun c : k => (1 : Matrix (Fin N) (Fin N) k) + c • X :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hev : ∀ᶠ c in 𝓝[≠] (0 : k), (1 : Matrix (Fin N) (Fin N) k) + c • X ∈ O := by
    have : ∀ᶠ c in 𝓝 (0 : k), (1 : Matrix (Fin N) (Fin N) k) + c • X ∈ O :=
      hcont.continuousAt.eventually_mem (hO.mem_nhds (by simpa using h1O))
    exact this.filter_mono nhdsWithin_le_nhds
  obtain ⟨c, hcO, hc0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hc0' : c ≠ 0 := hc0
  obtain ⟨v, hv, hvN⟩ := exists_one_add_smul_mem_unipRad (stdBlocks d hd) hn c
  have hvJ : v ∈ J := (memJ v).2 (by rw [hv]; exact hcO)
  let U : Set (GL (Fin N) k) := (fun g : GL (Fin N) k =>
    (1 : Matrix (Fin N) (Fin N) k) + c⁻¹ • ((g : Matrix (Fin N) (Fin N) k) - 1)) ⁻¹' O
  have hU : IsOpen U := by
    refine hO.preimage ?_
    have hs : Continuous fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) - 1 :=
      Units.continuous_val.sub continuous_const
    exact continuous_const.add (hs.const_smul c⁻¹)
  have h1U : (1 : GL (Fin N) k) ∈ U := by
    show (1 : Matrix (Fin N) (Fin N) k) + c⁻¹ • (((1 : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1) ∈ O
    simpa using h1O
  obtain ⟨j, hj⟩ := ht.2 U hU h1U
  refine ⟨j, ?_⟩
  have hconjAll : ∀ r : ℕ, leviEmb k (stdBlocks d hd) t ^ r * v *
      (leviEmb k (stdBlocks d hd) t ^ r)⁻¹ ∈ KN k N J d hd := by
    intro r
    induction r with
    | zero => simpa only [pow_zero, one_mul, inv_one, mul_one] using
        (show v ∈ KN k N J d hd from Subgroup.mem_inf.2 ⟨hvJ, hvN⟩)
    | succ r ih =>
      simpa only [pow_succ', _root_.mul_inv_rev, mul_assoc] using ht.1.1 _ ih
  set G := leviEmb k (stdBlocks d hd) t ^ j with hG
  have hconj : G * v * G⁻¹ ∈ KN k N J d hd := hconjAll j
  have hmem := hj v (Subgroup.mem_inf.2 ⟨hvJ, hvN⟩)
  have hval := val_conj_one_add_smul G n v c hv
  have hscaled : (1 : Matrix (Fin N) (Fin N) k) +
      c⁻¹ • (((G * v * G⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1) =
      ((G * n * G⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
    rw [hval]
    simp [smul_smul, inv_mul_cancel₀ hc0']
  obtain ⟨w, hw, hwN⟩ := exists_one_add_smul_mem_unipRad (stdBlocks d hd)
    (Subgroup.mem_inf.1 hconj).2 c⁻¹
  have hw_eq : w = G * n * G⁻¹ := by
    apply Units.ext
    exact hw.trans hscaled
  refine Subgroup.mem_inf.2 ⟨(memJ _).2 ?_, hw_eq ▸ hwN⟩
  have hmem' : (1 : Matrix (Fin N) (Fin N) k) +
      c⁻¹ • (((G * v * G⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1) ∈ O := hmem
  rw [hval] at hmem'
  simpa [smul_smul, inv_mul_cancel₀ hc0'] using hmem'

end GlobalTheory.CompanionTheory.ExpandN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaAEqOfUnip
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirabolic

variable {k : Type} [Field k]

theorem thetaA_eq_of_unip (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (x : MirUin k n)
    (w : Multiplicative (Fin n → k))
    (hx : ((x : Mir k n) : GL (Fin (n + 1)) k) = unip k n w) :
    thetaA k ψ a x = Circle.toUnits (ψ (a ⬝ᵥ w.toAdd)) := by
  have key : (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) x) = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    exact hx
  show Circle.toUnits (ψ (a ⬝ᵥ ((unipEquiv k n).symm
    ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) x)).toAdd)) = _
  rw [key]

theorem thetaConj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : ThetaConj k := by
  intro ψ n a m u
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  have e : glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ =
      unip k n (Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k).mulVec v.toAdd)) := by
    rw [hv', glEmb_mul_unip', mul_inv_cancel_right]
  have h : levi k n m * (u : Mir k n) * (levi k n m)⁻¹ ∈ MirUin k n := by
    show glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ ∈ MirU k n
    rw [e]
    exact ⟨_, rfl⟩
  refine ⟨h, ?_⟩
  rw [thetaA_eq_of_unip ψ _ u v hv', thetaA_eq_of_unip ψ a ⟨_, h⟩ _ e]
  simp only [toAdd_ofAdd]
  rw [dotProduct_mulVec]

end GlobalTheory.CompanionTheory.BZMirabolic

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZFun

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lastCol {n : ℕ} (u : MirUin k n) : Fin n → k :=
  fun i => (((u : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)

theorem continuous_lastCol (n : ℕ) : Continuous (lastCol k (n := n)) := by
  refine continuous_pi fun i => ?_
  have h : Continuous fun u : MirUin k n =>
      (((u : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact h.matrix_elem _ _

theorem thetaA_apply (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (u : MirUin k n) :
    thetaA k ψ a u = Circle.toUnits (ψ (a ⬝ᵥ lastCol k u)) := by
  obtain ⟨w, hw⟩ : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n := Subgroup.mem_subgroupOf.1 u.2
  have key : (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u) = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    exact hw.symm
  have hcol : lastCol k u = w.toAdd := by
    funext i
    simp only [lastCol, ← hw]
    exact unip_apply_castSucc_last k n w i
  show Circle.toUnits (ψ (a ⬝ᵥ ((unipEquiv k n).symm
    ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u)).toAdd)) = _
  rw [key, hcol]

theorem isOpen_addChar_eq_one (ψ : AddChar k Circle) (hψ : Continuous ψ) : IsOpen {x : k | ψ x = 1} := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : ψ x = 1 := hx
  have ht : Filter.Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
    simpa using (continuous_sub_right x).tendsto x
  filter_upwards [ht (cball_mem_nhds s)] with y hy
  have h1 : ψ (y - x) = 1 := hs _ hy
  have h2 : ψ y = ψ (y - x) * ψ x := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]
  show ψ y = 1
  rw [h2, h1, hx', one_mul]

theorem thetaOpen : ThetaOpen k := by
  intro ψ hψ n a
  have hc : Continuous fun u : MirUin k n => a ⬝ᵥ lastCol k u := by
    have h := continuous_lastCol k n
    simp only [dotProduct]
    exact continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).comp h)
  have he : ((thetaA k ψ a).ker : Set (MirUin k n)) =
      (fun u : MirUin k n => a ⬝ᵥ lastCol k u) ⁻¹' {x : k | ψ x = 1} := by
    ext u
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, thetaA_apply, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h
      apply Circle.ext
      simpa using congrArg Units.val h
    · intro h
      rw [h, map_one]
  rw [he]
  exact (isOpen_addChar_eq_one k ψ hψ).preimage hc

end GlobalTheory.CompanionTheory.BZFun

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedActionSmoothStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_action_smooth : ∀ {G M V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → ∀ (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G), Continuous s → ∀ (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n), IsSmooth (twAct ρ N θ s hs) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.twAct_isSmooth | exact GlobalTheory.CompanionTheory.BZMir.twAct_isSmooth | (intros; apply GlobalTheory.CompanionTheory.BZMir.twAct_isSmooth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantSmallBoxes
section
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

theorem exists_mem_twKer_box (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V)
    (χ : Multiplicative (Fin n → k) →* ℂˣ) (v : V)
    (hv : v ∈ twKer ρ ⊤ (χ.comp (⊤ : Subgroup (Multiplicative (Fin n → k))).subtype)) :
    ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (χ.comp (box k n j').subtype) := by
  classical
  have hmem : ∀ x : Multiplicative (Fin n → k), ∃ N : ℤ, x ∈ box k n N := by
    intro x
    choose m hm using fun i => exists_mem_valBall_neg_nat (K := k) (Multiplicative.toAdd x i)
    refine ⟨-((∑ i, m i : ℕ) : ℤ), (mem_box k).2 fun i => ?_⟩
    have h1 := hm i
    have hle : m i ≤ ∑ j, m j := Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)
    change normalizedValuation k _ ≤ WithZero.exp (-(-((m i : ℕ) : ℤ))) at h1
    change normalizedValuation k _ ≤ WithZero.exp (-(-((∑ j, m j : ℕ) : ℤ)))
    refine h1.trans (WithZero.exp_le_exp.2 ?_)
    simp only [neg_neg]
    exact_mod_cast hle
  unfold GlobalTheory.PRep.twKer at hv ⊢
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, u, rfl⟩ := hx
    obtain ⟨N, hN⟩ := hmem g.1
    exact ⟨N, fun j' hj' => Submodule.subset_span ⟨⟨g.1, box_antitone k n hj' hN⟩, u, rfl⟩⟩
  | zero => exact ⟨0, fun j' _ => Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, fun j' hj' => Submodule.add_mem _ (ha j' (hj'.trans (min_le_left _ _)))
      (hb j' (hj'.trans (min_le_right _ _)))⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, fun j' hj' => Submodule.smul_mem _ c (ha j' hj')⟩

end GlobalTheory.CompanionTheory.MirFourier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotientStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_occurs_of_subquotient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth π → IsSubquotient σ π → ∀ w : List (IrrGL (k := k)), Wd σ w → Wd π w := by
  first | exact @GlobalTheory.CompanionTheory.Words.wd_of_isSubquotient | exact GlobalTheory.CompanionTheory.Words.wd_of_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.Words.wd_of_isSubquotient <;> assumption)
end

